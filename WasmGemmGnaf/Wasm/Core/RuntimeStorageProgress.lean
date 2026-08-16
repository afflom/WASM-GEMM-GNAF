import WasmGemmGnaf.Wasm.Core.RuntimeInstrProgress

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-!
# Progress for store-backed source instructions

The lemmas in this file keep runtime alignment explicit.  Each store-backed
instruction receives the concrete module-address and store-instance lookup it
uses; later active-configuration typing can project those facts without
placing a progress conclusion in the invariant itself.
-/

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Source typing at an address type exposes the exact bounded address literal
used by the executable rules. -/
theorem SourceValOkA.addr_canonical {store : Store} {context : Context}
    {value : Val} {addressType : AddrType}
    (typed : SourceValOkA store context value addressType.toValType) :
    ∃ literal : AddrLit addressType,
      value = .num ⟨addrNumType addressType, addrLitToNum addressType literal⟩ := by
  cases addressType with
  | i32 =>
      obtain ⟨⟨value, bound⟩, hvalue⟩ := typed.num_canonical
      exact ⟨⟨value, bound⟩, by
        simpa [AddrType.toValType, AddrType.toNumType, addrNumType, addrSize,
          addrLitToNum] using hvalue⟩
  | i64 =>
      obtain ⟨⟨value, bound⟩, hvalue⟩ := typed.num_canonical
      exact ⟨⟨value, bound⟩, by
        simpa [AddrType.toValType, AddrType.toNumType, addrNumType, addrSize,
          addrLitToNum] using hvalue⟩

/-- Pointwise source typing of two operands exposes both values in source
order. -/
theorem SourceValuesOkA.pair_iff {store : Store} {context : Context}
    {values : List Val} {firstType secondType : ValType} :
    SourceValuesOkA store context values [firstType, secondType] ↔
      ∃ first second, values = [first, second] ∧
        SourceValOkA store context first firstType ∧
          SourceValOkA store context second secondType := by
  constructor
  · intro typed
    obtain ⟨firsts, seconds, hvalues, firstTyped, secondTyped⟩ :=
      typed.split (leftTypes := [firstType]) (rightTypes := [secondType])
    obtain ⟨first, hfirsts, firstValueTyped⟩ :=
      SourceValuesOkA.singleton_iff.mp firstTyped
    obtain ⟨second, hseconds, secondValueTyped⟩ :=
      SourceValuesOkA.singleton_iff.mp secondTyped
    subst firsts
    subst seconds
    exact ⟨first, second, hvalues, firstValueTyped, secondValueTyped⟩
  · rintro ⟨first, second, rfl, firstTyped, secondTyped⟩
    exact (SourceValuesOkA.singleton_iff.mpr ⟨first, rfl, firstTyped⟩).append
      (SourceValuesOkA.singleton_iff.mpr ⟨second, rfl, secondTyped⟩)

/-- Pointwise source typing of three operands exposes all values in source
order. -/
theorem SourceValuesOkA.triple_iff {store : Store} {context : Context}
    {values : List Val} {firstType secondType thirdType : ValType} :
    SourceValuesOkA store context values [firstType, secondType, thirdType] ↔
      ∃ first second third, values = [first, second, third] ∧
        SourceValOkA store context first firstType ∧
          SourceValOkA store context second secondType ∧
            SourceValOkA store context third thirdType := by
  constructor
  · intro typed
    obtain ⟨firsts, rest, hvalues, firstTyped, restTyped⟩ :=
      typed.split
        (leftTypes := [firstType])
        (rightTypes := [secondType, thirdType])
    obtain ⟨first, hfirsts, firstValueTyped⟩ :=
      SourceValuesOkA.singleton_iff.mp firstTyped
    obtain ⟨second, third, hrest, secondTyped, thirdTyped⟩ :=
      SourceValuesOkA.pair_iff.mp restTyped
    subst firsts
    subst rest
    exact ⟨first, second, third, hvalues, firstValueTyped,
      secondTyped, thirdTyped⟩
  · rintro ⟨first, second, third, rfl, firstTyped, secondTyped, thirdTyped⟩
    exact (SourceValuesOkA.singleton_iff.mpr ⟨first, rfl, firstTyped⟩).append
      ((SourceValuesOkA.singleton_iff.mpr ⟨second, rfl, secondTyped⟩).append
        (SourceValuesOkA.singleton_iff.mpr ⟨third, rfl, thirdTyped⟩))

/-- An aligned in-bounds memory window computes an actual `withMem` target.
This is only the constructive store update used by write instructions. -/
theorem State.withMem_exists_of_aligned
    {state : State} {index : MemIdx} {address : MemAddr}
    {memoryInstance : MemInst} {offset width : Nat} {replacement : List Byte}
    (hmodule : state.frame.mod.mems[index.val]? = some address)
    (hstore : state.store.mems[address]? = some memoryInstance)
    (hbound : offset + width ≤ memoryInstance.bytes.length) :
    ∃ target, state.withMem index offset width replacement = some target := by
  have haddress : address < state.store.mems.length :=
    (List.getElem?_eq_some_iff.mp hstore).1
  let spliced := memoryInstance.bytes.take offset ++ replacement ++
    memoryInstance.bytes.drop (offset + width)
  let updatedMems := state.store.mems.set address
    { memoryInstance with bytes := spliced }
  let target : State :=
    { state with store := { state.store with mems := updatedMems } }
  have hsplice : spliceAt? memoryInstance.bytes offset width replacement =
      some spliced := by
    simp [spliceAt?, hbound, spliced]
  have hset : setAt? state.store.mems address
      { memoryInstance with bytes := spliced } = some updatedMems := by
    simp [setAt?, haddress, updatedMems]
  refine ⟨target, ?_⟩
  simp [State.withMem, hmodule, hstore, hsplice, hset, target]

/-- A source-typed global read progresses once the indexed runtime global is
aligned with an actual store instance. -/
theorem Instr_okA.globalGet_source_progress
    {context : Context} {state : State} {index : GlobalIdx}
    {instructionType : InstrType} {values : List Val}
    {address : GlobalAddr} {globalInstance : GlobalInst}
    (typed : Instr_okA context (.globalGet index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.globals[index.val]? = some address)
    (hstore : state.store.globals[address]? = some globalInstance) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.globalGet index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | global_get hglobal =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      have hlookup : state.globalOf index = some globalInstance := by
        simp [State.globalOf, hmodule, hstore]
      have read : Step_readA state .globalGet
          [.plain (.globalGet index)] [globalInstance.value.toAdmin] :=
        .globalGet hlookup
      exact ⟨.read .globalGet _, (state, [globalInstance.value.toAdmin]),
        .read read⟩

/-- A source-typed mutable-global write targets an in-range store slot and
therefore computes an exact updated state. -/
theorem Instr_okA.globalSet_source_progress
    {context : Context} {state : State} {index : GlobalIdx}
    {instructionType : InstrType} {values : List Val}
    {address : GlobalAddr} {globalInstance : GlobalInst}
    (typed : Instr_okA context (.globalSet index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.globals[index.val]? = some address)
    (hstore : state.store.globals[address]? = some globalInstance) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.globalSet index)]) event target := by
  cases typed with
  | global_set hglobal =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      subst values
      have haddress : address < state.store.globals.length :=
        (List.getElem?_eq_some_iff.mp hstore).1
      let updatedGlobals := state.store.globals.set address
        { globalInstance with value := value }
      let targetState : State :=
        { state with store := { state.store with globals := updatedGlobals } }
      have hset : setAt? state.store.globals address
          { globalInstance with value := value } = some updatedGlobals := by
        simp [setAt?, haddress, updatedGlobals]
      have hupdate : state.withGlobal index value = some targetState := by
        simp [State.withGlobal, hmodule, hstore, hset, targetState]
      have step : StepA
          (state, [value.toAdmin, .plain (.globalSet index)])
          (.globalSet index) (targetState, []) := .globalSet hupdate
      exact ⟨.globalSet index, (targetState, []),
        by simpa [vals] using step⟩

/-- A source-typed table read either traps at an out-of-range address or reads
the concrete aligned table element. -/
theorem Instr_okA.tableGet_source_progress
    {context : Context} {state : State} {index : TableIdx}
    {instructionType : InstrType} {values : List Val}
    {address : TableAddr} {tableInstance : TableInst}
    (typed : Instr_okA context (.tableGet index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.tables[index.val]? = some address)
    (hstore : state.store.tables[address]? = some tableInstance) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.tableGet index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @table_get _ _ tableType htable =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨literal, hvalue⟩ := valueTyped.addr_canonical
      subst value
      subst values
      have hlookup : state.tableOf index = some tableInstance := by
        simp [State.tableOf, hmodule, hstore]
      by_cases hbound : literal.val < tableInstance.refs.length
      · let reference := tableInstance.refs[literal.val]
        have href : tableInstance.refs[literal.val]? = some reference :=
          List.getElem?_eq_getElem hbound
        have read : Step_readA state .tableGetVal
            [constAddr tableType.addr literal, .plain (.tableGet index)]
            [reference.toAdmin] := .tableGetVal hlookup href
        exact ⟨.read .tableGetVal _, (state, [reference.toAdmin]),
          by simpa [vals] using StepA.read read⟩
      · have hoob : literal.val ≥ tableInstance.refs.length :=
          Nat.le_of_not_gt hbound
        have read : Step_readA state .tableGetOob
            [constAddr tableType.addr literal, .plain (.tableGet index)]
            [.trap] := .tableGetOob hlookup hoob
        exact ⟨.read .tableGetOob _, (state, [.trap]),
          by simpa [vals] using StepA.read read⟩

/-- A source-typed table write either traps out of bounds or computes the exact
updated table store. -/
theorem Instr_okA.tableSet_source_progress
    {context : Context} {state : State} {index : TableIdx}
    {instructionType : InstrType} {values : List Val}
    {address : TableAddr} {tableInstance : TableInst}
    (typed : Instr_okA context (.tableSet index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.tables[index.val]? = some address)
    (hstore : state.store.tables[address]? = some tableInstance) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.tableSet index)]) event target := by
  cases typed with
  | @table_set _ _ tableType htable =>
      obtain ⟨addresses, references, hvalues, addressTyped, referenceTyped⟩ :=
        valuesTyped.split
          (leftTypes := [tableType.addr.toValType])
          (rightTypes := [.ref tableType.elem])
      obtain ⟨addressValue, haddresses, addressValueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp addressTyped
      obtain ⟨referenceValue, hreferences, referenceValueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp referenceTyped
      obtain ⟨literal, haddressValue⟩ := addressValueTyped.addr_canonical
      obtain ⟨reference, hreferenceValue⟩ := referenceValueTyped.ref_canonical
      subst addressValue
      subst referenceValue
      subst addresses
      subst references
      subst values
      have hlookup : state.tableOf index = some tableInstance := by
        simp [State.tableOf, hmodule, hstore]
      by_cases hbound : literal.val < tableInstance.refs.length
      · have htableAddress : address < state.store.tables.length :=
          (List.getElem?_eq_some_iff.mp hstore).1
        let updatedRefs := tableInstance.refs.set literal.val reference
        let updatedTables := state.store.tables.set address
          { tableInstance with refs := updatedRefs }
        let targetState : State :=
          { state with store := { state.store with tables := updatedTables } }
        have hrefs : setAt? tableInstance.refs literal.val reference =
            some updatedRefs := by
          simp [setAt?, hbound, updatedRefs]
        have htables : setAt? state.store.tables address
            { tableInstance with refs := updatedRefs } = some updatedTables := by
          simp [setAt?, htableAddress, updatedTables]
        have hupdate : state.withTable index literal.val reference =
            some targetState := by
          simp [State.withTable, hmodule, hstore, hrefs, htables, targetState]
        exact ⟨.tableSetVal index, (targetState, []),
          by simpa [vals] using
            (StepA.tableSetVal hlookup hbound hupdate)⟩
      · have hoob : literal.val ≥ tableInstance.refs.length :=
          Nat.le_of_not_gt hbound
        exact ⟨.tableSetOob index, (state, [.trap]),
          by simpa [vals] using (StepA.tableSetOob hlookup hoob)⟩

/-- A table-size read progresses once the runtime instance's address type and
representable length are retained by the alignment invariant. -/
theorem Instr_okA.tableSize_source_progress
    {context : Context} {state : State} {index : TableIdx}
    {instructionType : InstrType} {values : List Val}
    {address : TableAddr} {tableInstance : TableInst}
    {size : AddrLit tableInstance.type.addr}
    (typed : Instr_okA context (.tableSize index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.tables[index.val]? = some address)
    (hstore : state.store.tables[address]? = some tableInstance)
    (hsize : tableInstance.refs.length = size.val) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.tableSize index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | table_size htable =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      have hlookup : state.tableOf index = some tableInstance := by
        simp [State.tableOf, hmodule, hstore]
      have read : Step_readA state .tableSize [.plain (.tableSize index)]
          [constAddr tableInstance.type.addr size] :=
        .tableSize hlookup hsize rfl
      exact ⟨.read .tableSize _,
        (state, [constAddr tableInstance.type.addr size]), .read read⟩

/-- The authority permits a table growth request to fail, hence every
source-typed request with canonical operands has an immediate successor. -/
theorem Instr_okA.tableGrow_source_progress
    {context : Context} {state : State} {index : TableIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.tableGrow index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.tableGrow index)]) event target := by
  cases typed with
  | @table_grow _ _ tableType htable =>
      obtain ⟨references, lengths, hvalues, referenceTyped, lengthTyped⟩ :=
        valuesTyped.split
          (leftTypes := [.ref tableType.elem])
          (rightTypes := [tableType.addr.toValType])
      obtain ⟨referenceValue, hreferences, referenceValueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp referenceTyped
      obtain ⟨lengthValue, hlengths, lengthValueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp lengthTyped
      obtain ⟨reference, hreferenceValue⟩ := referenceValueTyped.ref_canonical
      obtain ⟨length, hlengthValue⟩ := lengthValueTyped.addr_canonical
      subst referenceValue
      subst lengthValue
      subst references
      subst lengths
      subst values
      let failure : AddrLit tableType.addr :=
        Numerics.inv_signed_ (addrSize tableType.addr) (-1)
      exact ⟨.tableGrowFail index length.val,
        (state, [constAddr tableType.addr failure]),
        by simpa [vals] using
          (StepA.tableGrowFail (x := index) (r := reference)
            (n := length) (e := failure) rfl)⟩

/-- A table fill either traps, terminates at zero length, or unfolds one
in-bounds element.  The strict runtime capacity bound makes the emitted
successor address representable in the table's source address type. -/
theorem Instr_okA.tableFill_source_progress
    {context : Context} {state : State} {index : TableIdx}
    {instructionType : InstrType} {values : List Val}
    {address : TableAddr} {tableInstance : TableInst}
    (typed : Instr_okA context (.tableFill index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.tables[index.val]? = some address)
    (hstore : state.store.tables[address]? = some tableInstance)
    (hcapacity : ∀ {tableType : TableType},
      context.tables[index.val]? = some tableType →
        tableInstance.refs.length < 2 ^ addrSize tableType.addr) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.tableFill index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @table_fill _ _ tableType htable =>
      obtain ⟨addressValue, referenceValue, lengthValue, hvalues,
          addressTyped, referenceTyped, lengthTyped⟩ :=
        SourceValuesOkA.triple_iff.mp valuesTyped
      obtain ⟨start, haddressValue⟩ := addressTyped.addr_canonical
      obtain ⟨reference, hreferenceValue⟩ := referenceTyped.ref_canonical
      obtain ⟨length, hlengthValue⟩ := lengthTyped.addr_canonical
      subst addressValue
      subst referenceValue
      subst lengthValue
      subst values
      have hlookup : state.tableOf index = some tableInstance := by
        simp [State.tableOf, hmodule, hstore]
      by_cases hoob : start.val + length.val > tableInstance.refs.length
      · have read : Step_readA state .tableFillOob
            [constAddr tableType.addr start, reference.toAdmin,
              constAddr tableType.addr length, .plain (.tableFill index)]
            [.trap] := .tableFillOob hlookup hoob
        exact ⟨.read .tableFillOob _, (state, [.trap]),
          by simpa [vals] using StepA.read read⟩
      · by_cases hzero : length.val = 0
        · have read : Step_readA state .tableFillZero
              [constAddr tableType.addr start, reference.toAdmin,
                constAddr tableType.addr length, .plain (.tableFill index)]
              [] := .tableFillZero hlookup hoob hzero
          exact ⟨.read .tableFillZero _, (state, []),
            by simpa [vals] using StepA.read read⟩
        · have hcapacity' : tableInstance.refs.length <
              2 ^ addrSize tableType.addr := hcapacity htable
          have hstartBound : start.val + 1 <
              2 ^ addrSize tableType.addr := by
            omega
          have hlengthBound : length.val - 1 <
              2 ^ addrSize tableType.addr :=
            Nat.lt_of_le_of_lt (Nat.sub_le length.val 1) length.property
          let nextStart : AddrLit tableType.addr :=
            ⟨start.val + 1, hstartBound⟩
          let nextLength : AddrLit tableType.addr :=
            ⟨length.val - 1, hlengthBound⟩
          have hnextLength : length.val = nextLength.val + 1 := by
            dsimp [nextLength]
            omega
          have read : Step_readA state .tableFillSucc
              [constAddr tableType.addr start, reference.toAdmin,
                constAddr tableType.addr length, .plain (.tableFill index)]
              [constAddr tableType.addr start, reference.toAdmin,
                .plain (.tableSet index),
                constAddr tableType.addr nextStart, reference.toAdmin,
                constAddr tableType.addr nextLength,
                .plain (.tableFill index)] :=
            .tableFillSucc hlookup hoob hzero rfl hnextLength
          exact ⟨.read .tableFillSucc _,
            (state,
              [constAddr tableType.addr start, reference.toAdmin,
                .plain (.tableSet index),
                constAddr tableType.addr nextStart, reference.toAdmin,
                constAddr tableType.addr nextLength,
                .plain (.tableFill index)]),
            by simpa [vals] using StepA.read read⟩

/-- A table copy either traps, terminates at zero length, or unfolds in the
direction required for overlap safety.  Strict aligned capacities make every
emitted address literal representable. -/
theorem Instr_okA.tableCopy_source_progress
    {context : Context} {state : State} {targetIndex sourceIndex : TableIdx}
    {instructionType : InstrType} {values : List Val}
    {targetAddress sourceAddress : TableAddr}
    {targetInstance sourceInstance : TableInst}
    (typed : Instr_okA context (.tableCopy targetIndex sourceIndex)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (htargetModule : state.frame.mod.tables[targetIndex.val]? =
      some targetAddress)
    (hsourceModule : state.frame.mod.tables[sourceIndex.val]? =
      some sourceAddress)
    (htargetStore : state.store.tables[targetAddress]? = some targetInstance)
    (hsourceStore : state.store.tables[sourceAddress]? = some sourceInstance)
    (htargetCapacity : ∀ {tableType : TableType},
      context.tables[targetIndex.val]? = some tableType →
        targetInstance.refs.length < 2 ^ addrSize tableType.addr)
    (hsourceCapacity : ∀ {tableType : TableType},
      context.tables[sourceIndex.val]? = some tableType →
        sourceInstance.refs.length < 2 ^ addrSize tableType.addr) :
    ∃ event target,
      StepA
        (state, vals values ++
          [.plain (.tableCopy targetIndex sourceIndex)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @table_copy _ _ _ targetType sourceType htargetType hsourceType hsubtype =>
      obtain ⟨targetValue, sourceValue, lengthValue, hvalues,
          targetTyped, sourceTyped, lengthTyped⟩ :=
        SourceValuesOkA.triple_iff.mp valuesTyped
      obtain ⟨targetStart, htargetValue⟩ := targetTyped.addr_canonical
      obtain ⟨sourceStart, hsourceValue⟩ := sourceTyped.addr_canonical
      obtain ⟨length, hlengthValue⟩ := lengthTyped.addr_canonical
      subst targetValue
      subst sourceValue
      subst lengthValue
      subst values
      have htargetLookup : state.tableOf targetIndex = some targetInstance := by
        simp [State.tableOf, htargetModule, htargetStore]
      have hsourceLookup : state.tableOf sourceIndex = some sourceInstance := by
        simp [State.tableOf, hsourceModule, hsourceStore]
      let badBounds :=
        targetStart.val + length.val > targetInstance.refs.length ∨
          sourceStart.val + length.val > sourceInstance.refs.length
      by_cases hoob : badBounds
      · have read : Step_readA state .tableCopyOob
            [constAddr targetType.addr targetStart,
              constAddr sourceType.addr sourceStart,
              constAddr (AddrType.min targetType.addr sourceType.addr) length,
              .plain (.tableCopy targetIndex sourceIndex)] [.trap] :=
          .tableCopyOob htargetLookup hsourceLookup hoob
        exact ⟨.read .tableCopyOob _, (state, [.trap]),
          by simpa [vals] using StepA.read read⟩
      · by_cases hzero : length.val = 0
        · have read : Step_readA state .tableCopyZero
              [constAddr targetType.addr targetStart,
                constAddr sourceType.addr sourceStart,
                constAddr (AddrType.min targetType.addr sourceType.addr) length,
                .plain (.tableCopy targetIndex sourceIndex)] [] :=
            .tableCopyZero htargetLookup hsourceLookup hoob hzero
          exact ⟨.read .tableCopyZero _, (state, []),
            by simpa [vals] using StepA.read read⟩
        · have htargetBound : targetStart.val + 1 <
              2 ^ addrSize targetType.addr := by
            have := htargetCapacity htargetType
            dsimp [badBounds] at hoob
            omega
          have hsourceBound : sourceStart.val + 1 <
              2 ^ addrSize sourceType.addr := by
            have := hsourceCapacity hsourceType
            dsimp [badBounds] at hoob
            omega
          have hlengthBound : length.val - 1 <
              2 ^ addrSize (AddrType.min targetType.addr sourceType.addr) :=
            Nat.lt_of_le_of_lt (Nat.sub_le length.val 1) length.property
          let nextTarget : AddrLit targetType.addr :=
            ⟨targetStart.val + 1, htargetBound⟩
          let nextSource : AddrLit sourceType.addr :=
            ⟨sourceStart.val + 1, hsourceBound⟩
          let nextLength :
              AddrLit (AddrType.min targetType.addr sourceType.addr) :=
            ⟨length.val - 1, hlengthBound⟩
          have hnextLength : length.val = nextLength.val + 1 := by
            dsimp [nextLength]
            omega
          by_cases hle : targetStart.val ≤ sourceStart.val
          · have read : Step_readA state .tableCopyLe
                [constAddr targetType.addr targetStart,
                  constAddr sourceType.addr sourceStart,
                  constAddr (AddrType.min targetType.addr sourceType.addr) length,
                  .plain (.tableCopy targetIndex sourceIndex)]
                [constAddr targetType.addr targetStart,
                  constAddr sourceType.addr sourceStart,
                  .plain (.tableGet sourceIndex), .plain (.tableSet targetIndex),
                  constAddr targetType.addr nextTarget,
                  constAddr sourceType.addr nextSource,
                  constAddr (AddrType.min targetType.addr sourceType.addr) nextLength,
                  .plain (.tableCopy targetIndex sourceIndex)] :=
              .tableCopyLe htargetLookup hsourceLookup hoob hzero hle
                rfl rfl hnextLength
            exact ⟨.read .tableCopyLe _,
              (state,
                [constAddr targetType.addr targetStart,
                  constAddr sourceType.addr sourceStart,
                  .plain (.tableGet sourceIndex), .plain (.tableSet targetIndex),
                  constAddr targetType.addr nextTarget,
                  constAddr sourceType.addr nextSource,
                  constAddr (AddrType.min targetType.addr sourceType.addr) nextLength,
                  .plain (.tableCopy targetIndex sourceIndex)]),
              by simpa [vals] using StepA.read read⟩
          · have htargetEndBound : targetStart.val + length.val - 1 <
                2 ^ addrSize targetType.addr := by
              have := htargetCapacity htargetType
              dsimp [badBounds] at hoob
              omega
            have hsourceEndBound : sourceStart.val + length.val - 1 <
                2 ^ addrSize sourceType.addr := by
              have := hsourceCapacity hsourceType
              dsimp [badBounds] at hoob
              omega
            let targetEnd : AddrLit targetType.addr :=
              ⟨targetStart.val + length.val - 1, htargetEndBound⟩
            let sourceEnd : AddrLit sourceType.addr :=
              ⟨sourceStart.val + length.val - 1, hsourceEndBound⟩
            have htargetEnd : targetEnd.val + 1 =
                targetStart.val + length.val := by
              dsimp [targetEnd]
              omega
            have hsourceEnd : sourceEnd.val + 1 =
                sourceStart.val + length.val := by
              dsimp [sourceEnd]
              omega
            have read : Step_readA state .tableCopyGt
                [constAddr targetType.addr targetStart,
                  constAddr sourceType.addr sourceStart,
                  constAddr (AddrType.min targetType.addr sourceType.addr) length,
                  .plain (.tableCopy targetIndex sourceIndex)]
                [constAddr targetType.addr targetEnd,
                  constAddr sourceType.addr sourceEnd,
                  .plain (.tableGet sourceIndex), .plain (.tableSet targetIndex),
                  constAddr targetType.addr targetStart,
                  constAddr sourceType.addr sourceStart,
                  constAddr (AddrType.min targetType.addr sourceType.addr) nextLength,
                  .plain (.tableCopy targetIndex sourceIndex)] :=
              .tableCopyGt htargetLookup hsourceLookup hoob hzero hle
                htargetEnd hsourceEnd hnextLength
            exact ⟨.read .tableCopyGt _,
              (state,
                [constAddr targetType.addr targetEnd,
                  constAddr sourceType.addr sourceEnd,
                  .plain (.tableGet sourceIndex), .plain (.tableSet targetIndex),
                  constAddr targetType.addr targetStart,
                  constAddr sourceType.addr sourceStart,
                  constAddr (AddrType.min targetType.addr sourceType.addr) nextLength,
                  .plain (.tableCopy targetIndex sourceIndex)]),
              by simpa [vals] using StepA.read read⟩

/-- Initializing a table from an aligned element segment either traps,
terminates at zero length, or unfolds one concrete reference transfer. -/
theorem Instr_okA.tableInit_source_progress
    {context : Context} {state : State} {tableIndex : TableIdx}
    {elementIndex : ElemIdx} {instructionType : InstrType} {values : List Val}
    {tableAddress : TableAddr} {elementAddress : ElemAddr}
    {tableInstance : TableInst} {elementInstance : ElemInst}
    (typed : Instr_okA context (.tableInit tableIndex elementIndex)
      instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (htableModule : state.frame.mod.tables[tableIndex.val]? = some tableAddress)
    (helemModule : state.frame.mod.elems[elementIndex.val]? = some elementAddress)
    (htableStore : state.store.tables[tableAddress]? = some tableInstance)
    (helemStore : state.store.elems[elementAddress]? = some elementInstance)
    (htableCapacity : ∀ {tableType : TableType},
      context.tables[tableIndex.val]? = some tableType →
        tableInstance.refs.length < 2 ^ addrSize tableType.addr)
    (helemCapacity : elementInstance.refs.length < 2 ^ 32) :
    ∃ event target,
      StepA
        (state, vals values ++ [.plain (.tableInit tableIndex elementIndex)])
        event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @table_init _ _ _ tableType elementType htableType helemType hsubtype =>
      obtain ⟨tableValue, elementValue, lengthValue, hvalues,
          tableTyped, elementTyped, lengthTyped⟩ :=
        SourceValuesOkA.triple_iff.mp valuesTyped
      obtain ⟨tableStart, htableValue⟩ := tableTyped.addr_canonical
      obtain ⟨elementStart, helementValue⟩ := elementTyped.num_canonical
      obtain ⟨length, hlengthValue⟩ := lengthTyped.num_canonical
      subst tableValue
      subst elementValue
      subst lengthValue
      subst values
      have htableLookup : state.tableOf tableIndex = some tableInstance := by
        simp [State.tableOf, htableModule, htableStore]
      have helemLookup : state.elemOf elementIndex = some elementInstance := by
        simp [State.elemOf, helemModule, helemStore]
      let badBounds :=
        tableStart.val + length.val > tableInstance.refs.length ∨
          elementStart.val + length.val > elementInstance.refs.length
      by_cases hoob : badBounds
      · have read : Step_readA state .tableInitOob
            [constAddr tableType.addr tableStart, constI32 elementStart,
              constI32 length, .plain (.tableInit tableIndex elementIndex)]
            [.trap] := .tableInitOob htableLookup helemLookup hoob
        exact ⟨.read .tableInitOob _, (state, [.trap]),
          by simpa [vals] using StepA.read read⟩
      · by_cases hzero : length.val = 0
        · have read : Step_readA state .tableInitZero
              [constAddr tableType.addr tableStart, constI32 elementStart,
                constI32 length, .plain (.tableInit tableIndex elementIndex)]
              [] := .tableInitZero htableLookup helemLookup hoob hzero
          exact ⟨.read .tableInitZero _, (state, []),
            by simpa [vals] using StepA.read read⟩
        · have hreferenceBound : elementStart.val <
              elementInstance.refs.length := by
            dsimp [badBounds] at hoob
            omega
          let reference := elementInstance.refs[elementStart.val]
          have hreference : elementInstance.refs[elementStart.val]? =
              some reference := List.getElem?_eq_getElem hreferenceBound
          have htableNextBound : tableStart.val + 1 <
              2 ^ addrSize tableType.addr := by
            have := htableCapacity htableType
            dsimp [badBounds] at hoob
            omega
          have helemNextBound : elementStart.val + 1 < 2 ^ 32 := by
            dsimp [badBounds] at hoob
            omega
          have hlengthBound : length.val - 1 < 2 ^ 32 :=
            Nat.lt_of_le_of_lt (Nat.sub_le length.val 1) length.property
          let nextTable : AddrLit tableType.addr :=
            ⟨tableStart.val + 1, htableNextBound⟩
          let nextElement : U32 :=
            ⟨elementStart.val + 1, helemNextBound⟩
          let nextLength : U32 := ⟨length.val - 1, hlengthBound⟩
          have hnextLength : length.val = nextLength.val + 1 := by
            dsimp [nextLength]
            omega
          have read : Step_readA state .tableInitSucc
              [constAddr tableType.addr tableStart, constI32 elementStart,
                constI32 length, .plain (.tableInit tableIndex elementIndex)]
              [constAddr tableType.addr tableStart, reference.toAdmin,
                .plain (.tableSet tableIndex),
                constAddr tableType.addr nextTable, constI32 nextElement,
                constI32 nextLength,
                .plain (.tableInit tableIndex elementIndex)] :=
            .tableInitSucc htableLookup helemLookup hoob hzero hreference
              rfl rfl hnextLength
          exact ⟨.read .tableInitSucc _,
            (state,
              [constAddr tableType.addr tableStart, reference.toAdmin,
                .plain (.tableSet tableIndex),
                constAddr tableType.addr nextTable, constI32 nextElement,
                constI32 nextLength,
                .plain (.tableInit tableIndex elementIndex)]),
            by simpa [vals] using StepA.read read⟩

/-- Dropping an aligned element segment computes the exact store update. -/
theorem Instr_okA.elemDrop_source_progress
    {context : Context} {state : State} {index : ElemIdx}
    {instructionType : InstrType} {values : List Val}
    {address : ElemAddr} {elementInstance : ElemInst}
    (typed : Instr_okA context (.elemDrop index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.elems[index.val]? = some address)
    (hstore : state.store.elems[address]? = some elementInstance) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.elemDrop index)]) event target := by
  cases typed with
  | elem_drop helem =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      have haddress : address < state.store.elems.length :=
        (List.getElem?_eq_some_iff.mp hstore).1
      let updatedElems := state.store.elems.set address
        { elementInstance with refs := [] }
      let targetState : State :=
        { state with store := { state.store with elems := updatedElems } }
      have hset : setAt? state.store.elems address
          { elementInstance with refs := [] } = some updatedElems := by
        simp [setAt?, haddress, updatedElems]
      have hupdate : state.withElem index [] = some targetState := by
        simp [State.withElem, hmodule, hstore, hset, targetState]
      exact ⟨.elemDrop index, (targetState, []), StepA.elemDrop hupdate⟩

/-- A memory-size read progresses once the runtime instance's page count is
retained as a representable address literal. -/
theorem Instr_okA.memorySize_source_progress
    {context : Context} {state : State} {index : MemIdx}
    {instructionType : InstrType} {values : List Val}
    {address : MemAddr} {memoryInstance : MemInst}
    {pages : AddrLit memoryInstance.type.addr}
    (typed : Instr_okA context (.memorySize index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.mems[index.val]? = some address)
    (hstore : state.store.mems[address]? = some memoryInstance)
    (hpages : pages.val * (64 * Ki) = memoryInstance.bytes.length) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.memorySize index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | memory_size hmem =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      have hlookup : state.memOf index = some memoryInstance := by
        simp [State.memOf, hmodule, hstore]
      have read : Step_readA state .memorySize [.plain (.memorySize index)]
          [constAddr memoryInstance.type.addr pages] :=
        .memorySize hlookup hpages rfl
      exact ⟨.read .memorySize _,
        (state, [constAddr memoryInstance.type.addr pages]), .read read⟩

/-- The authority permits a memory growth request to fail, so every canonical
source-typed request has an immediate successor. -/
theorem Instr_okA.memoryGrow_source_progress
    {context : Context} {state : State} {index : MemIdx}
    {instructionType : InstrType} {values : List Val}
    (typed : Instr_okA context (.memoryGrow index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.memoryGrow index)]) event target := by
  cases typed with
  | @memory_grow _ _ memoryType hmem =>
      obtain ⟨value, hvalues, valueTyped⟩ :=
        SourceValuesOkA.singleton_iff.mp valuesTyped
      obtain ⟨pages, hvalue⟩ := valueTyped.addr_canonical
      subst value
      subst values
      let failure : AddrLit memoryType.addr :=
        Numerics.inv_signed_ (addrSize memoryType.addr) (-1)
      exact ⟨.memoryGrowFail index pages.val,
        (state, [constAddr memoryType.addr failure]),
        by simpa [vals] using
          (StepA.memoryGrowFail (x := index) (n := pages)
            (e := failure) rfl)⟩

/-- Below the full address-space boundary, memory fill has the same exact
trap/zero/successor trichotomy as the authority relation.  The strict capacity
premise records the presently known full-i32-memory boundary explicitly. -/
theorem Instr_okA.memoryFill_source_progress
    {context : Context} {state : State} {index : MemIdx}
    {instructionType : InstrType} {values : List Val}
    {address : MemAddr} {memoryInstance : MemInst}
    (typed : Instr_okA context (.memoryFill index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.mems[index.val]? = some address)
    (hstore : state.store.mems[address]? = some memoryInstance)
    (hcapacity : ∀ {memoryType : MemType},
      context.mems[index.val]? = some memoryType →
        memoryInstance.bytes.length < 2 ^ addrSize memoryType.addr) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.memoryFill index)]) event target := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases typed with
  | @memory_fill _ _ memoryType hmem =>
      obtain ⟨addressValue, byteValue, lengthValue, hvalues,
          addressTyped, byteTyped, lengthTyped⟩ :=
        SourceValuesOkA.triple_iff.mp valuesTyped
      obtain ⟨start, haddressValue⟩ := addressTyped.addr_canonical
      obtain ⟨length, hlengthValue⟩ := lengthTyped.addr_canonical
      subst addressValue
      subst lengthValue
      subst values
      have hlookup : state.memOf index = some memoryInstance := by
        simp [State.memOf, hmodule, hstore]
      by_cases hoob : start.val + length.val > memoryInstance.bytes.length
      · have read : Step_readA state .memoryFillOob
            [constAddr memoryType.addr start, byteValue.toAdmin,
              constAddr memoryType.addr length, .plain (.memoryFill index)]
            [.trap] := .memoryFillOob hlookup hoob
        exact ⟨.read .memoryFillOob _, (state, [.trap]),
          by simpa [vals] using StepA.read read⟩
      · by_cases hzero : length.val = 0
        · have read : Step_readA state .memoryFillZero
              [constAddr memoryType.addr start, byteValue.toAdmin,
                constAddr memoryType.addr length, .plain (.memoryFill index)]
              [] := .memoryFillZero hlookup hoob hzero
          exact ⟨.read .memoryFillZero _, (state, []),
            by simpa [vals] using StepA.read read⟩
        · have hstartBound : start.val + 1 <
              2 ^ addrSize memoryType.addr := by
            have := hcapacity hmem
            omega
          have hlengthBound : length.val - 1 <
              2 ^ addrSize memoryType.addr :=
            Nat.lt_of_le_of_lt (Nat.sub_le length.val 1) length.property
          let nextStart : AddrLit memoryType.addr :=
            ⟨start.val + 1, hstartBound⟩
          let nextLength : AddrLit memoryType.addr :=
            ⟨length.val - 1, hlengthBound⟩
          have hnextLength : length.val = nextLength.val + 1 := by
            dsimp [nextLength]
            omega
          have read : Step_readA state .memoryFillSucc
              [constAddr memoryType.addr start, byteValue.toAdmin,
                constAddr memoryType.addr length, .plain (.memoryFill index)]
              [constAddr memoryType.addr start, byteValue.toAdmin,
                .plain (.store .i32 (some ⟨.s8⟩) index MemArg.zero),
                constAddr memoryType.addr nextStart, byteValue.toAdmin,
                constAddr memoryType.addr nextLength,
                .plain (.memoryFill index)] :=
            .memoryFillSucc hlookup hoob hzero rfl hnextLength
          exact ⟨.read .memoryFillSucc _,
            (state,
              [constAddr memoryType.addr start, byteValue.toAdmin,
                .plain (.store .i32 (some ⟨.s8⟩) index MemArg.zero),
                constAddr memoryType.addr nextStart, byteValue.toAdmin,
                constAddr memoryType.addr nextLength,
                .plain (.memoryFill index)]),
            by simpa [vals] using StepA.read read⟩

/-- A full-width scalar store progresses from its exact source operand types
once the referenced runtime memory is aligned.  This helper is shared by the
two source typing constructors for an unpacked store. -/
theorem storeNum_source_progress_of_aligned
    {context : Context} {state : State} {numberType : NumType}
    {index : MemIdx} {argument : MemArg} {memoryType : MemType}
    {values : List Val} {address : MemAddr} {memoryInstance : MemInst}
    (valuesTyped : SourceValuesOkA state.store context values
      [memoryType.addr.toValType, .num numberType])
    (hmodule : state.frame.mod.mems[index.val]? = some address)
    (hstore : state.store.mems[address]? = some memoryInstance) :
    ∃ event target,
      StepA
        (state, vals values ++ [.plain (.store numberType none index argument)])
        event target := by
  obtain ⟨addressValue, storedValue, hvalues, addressTyped, storedTyped⟩ :=
    SourceValuesOkA.pair_iff.mp valuesTyped
  obtain ⟨start, haddressValue⟩ := addressTyped.addr_canonical
  obtain ⟨literal, hstoredValue⟩ := storedTyped.num_canonical
  subst addressValue
  subst storedValue
  subst values
  have hlookup : state.memOf index = some memoryInstance := by
    simp [State.memOf, hmodule, hstore]
  by_cases hoob : start.val + argument.offset.val + numberType.size / 8 >
      memoryInstance.bytes.length
  · exact ⟨.storeNumOob index (numberType.size / 8), (state, [.trap]),
      by simpa [vals] using (StepA.storeNumOob hlookup hoob)⟩
  · have hbound : start.val + argument.offset.val + numberType.size / 8 ≤
        memoryInstance.bytes.length := Nat.le_of_not_gt hoob
    obtain ⟨targetState, hupdate⟩ := State.withMem_exists_of_aligned
      hmodule hstore hbound
      (replacement := releasedNumerics.nbytes_ numberType literal)
    exact ⟨.storeNumVal index (numberType.size / 8), (targetState, []),
      by simpa [vals] using (StepA.storeNumVal rfl hupdate)⟩

/-- A full-width vector store progresses from its exact source operand types
once the referenced runtime memory is aligned. -/
theorem vstore_source_progress_of_aligned
    {context : Context} {state : State} {index : MemIdx} {argument : MemArg}
    {memoryType : MemType} {values : List Val}
    {address : MemAddr} {memoryInstance : MemInst}
    (valuesTyped : SourceValuesOkA state.store context values
      [memoryType.addr.toValType, ValType.v128])
    (hmodule : state.frame.mod.mems[index.val]? = some address)
    (hstore : state.store.mems[address]? = some memoryInstance) :
    ∃ event target,
      StepA
        (state, vals values ++ [.plain (.vstore .v128 index argument)])
        event target := by
  obtain ⟨addressValue, storedValue, hvalues, addressTyped, storedTyped⟩ :=
    SourceValuesOkA.pair_iff.mp valuesTyped
  obtain ⟨start, haddressValue⟩ := addressTyped.addr_canonical
  obtain ⟨literal, hstoredValue⟩ := storedTyped.vec_canonical
  subst addressValue
  subst storedValue
  subst values
  have hlookup : state.memOf index = some memoryInstance := by
    simp [State.memOf, hmodule, hstore]
  by_cases hoob : start.val + argument.offset.val + VecType.v128.size / 8 >
      memoryInstance.bytes.length
  · exact ⟨.vstoreOob index (VecType.v128.size / 8), (state, [.trap]),
      by simpa [vals] using (StepA.vstoreOob hlookup hoob)⟩
  · have hbound : start.val + argument.offset.val + VecType.v128.size / 8 ≤
        memoryInstance.bytes.length := Nat.le_of_not_gt hoob
    obtain ⟨targetState, hupdate⟩ := State.withMem_exists_of_aligned
      hmodule hstore hbound
      (replacement := releasedNumerics.vbytes_ .v128 literal)
    exact ⟨.vstoreVal index (VecType.v128.size / 8), (targetState, []),
      by simpa [vals] using (StepA.vstoreVal rfl hupdate)⟩

/-- Dropping an aligned data segment computes the exact store update. -/
theorem Instr_okA.dataDrop_source_progress
    {context : Context} {state : State} {index : DataIdx}
    {instructionType : InstrType} {values : List Val}
    {address : DataAddr} {dataInstance : DataInst}
    (typed : Instr_okA context (.dataDrop index) instructionType)
    (valuesTyped : SourceValuesOkA state.store context values
      instructionType.dom)
    (hmodule : state.frame.mod.datas[index.val]? = some address)
    (hstore : state.store.datas[address]? = some dataInstance) :
    ∃ event target,
      StepA (state, vals values ++ [.plain (.dataDrop index)]) event target := by
  cases typed with
  | data_drop hdata =>
      have hvalues : values = [] := valuesTyped.nil_values
      subst values
      have haddress : address < state.store.datas.length :=
        (List.getElem?_eq_some_iff.mp hstore).1
      let updatedDatas := state.store.datas.set address
        { dataInstance with bytes := [] }
      let targetState : State :=
        { state with store := { state.store with datas := updatedDatas } }
      have hset : setAt? state.store.datas address
          { dataInstance with bytes := [] } = some updatedDatas := by
        simp [setAt?, haddress, updatedDatas]
      have hupdate : state.withData index [] = some targetState := by
        simp [State.withData, hmodule, hstore, hset, targetState]
      exact ⟨.dataDrop index, (targetState, []), StepA.dataDrop hupdate⟩

end WasmGemmGnaf.Wasm.Core.Exec
