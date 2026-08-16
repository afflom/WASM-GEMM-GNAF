/-
  Executable successors for the store-reading Core rules.

  The result carrier retains the independent `StepA` derivation while the
  executable projection erases it.  This makes soundness structural: every
  emitted pair was constructed from the corresponding amended-Core rule.
-/
import WasmGemmGnaf.Wasm.Core.WholeSuccessors
import WasmGemmGnaf.Wasm.Core.RuntimeDecision
import WasmGemmGnaf.Wasm.Core.BinaryWellFormed

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec


/-- A computed successor together with its independently checked rule
derivation.  The proof is erased by code generation. -/
structure StepAResult (source : Config) where
  event : Event
  next : Config
  step : StepA source event next

/-- The executable pair carried by a certified successor. -/
def StepAResult.toPair {source : Config} (result : StepAResult source) :
    Event × Config :=
  (result.event, result.next)

/-- Transport a certified result across an exact reconstruction of its source
configuration. -/
def StepAResult.castSource {source rebuilt : Config}
    (result : StepAResult source) (h : source = rebuilt) :
    StepAResult rebuilt :=
  h ▸ result

/-- Package one store-reading rule as a labelled Core successor. -/
def readResult {z : State} {source target : List AdminInstr}
    (rule : ReadRule) (step : Step_readA z rule source target) :
    StepAResult (z, source) :=
  { event := .read rule (sourcePlains source)
    next := (z, target)
    step := .read step }

/-- Split a nonempty list into its initial segment and last element. -/
def splitLastValue? {α : Type} : List α → Option (List α × α)
  | [] => none
  | [a] => some ([], a)
  | a :: as => (splitLastValue? as).map fun pair => (a :: pair.1, pair.2)

theorem splitLastValue?_eq_append {α : Type} :
    ∀ {xs initial : List α} {last : α},
      splitLastValue? xs = some (initial, last) → xs = initial ++ [last]
  | [], _, _, h => by simp [splitLastValue?] at h
  | [x], initial, last, h => by
      simp only [splitLastValue?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | x :: y :: xs, initial, last, h => by
      simp only [splitLastValue?] at h
      cases hrest : splitLastValue? (y :: xs) with
      | none => simp [hrest] at h
      | some pair =>
          rcases pair with ⟨rest, final⟩
          simp only [hrest, Option.map, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rw [splitLastValue?_eq_append hrest]
          simp

/-- The concrete candidate whose little-endian bytes may satisfy a scalar
load rule.  Equality is checked again at the rule boundary, so this total
decoder cannot emit an unsound successor. -/
def numOfBytes? : (type : NumType) → List Byte → Option (Num_ type)
  | .i32, bytes => some (Numerics.ofNatWrap 32 (Binary.leNat bytes))
  | .i64, bytes => some (Numerics.ofNatWrap 64 (Binary.leNat bytes))
  | .f32, bytes => Binary.invFbytes 32 bytes
  | .f64, bytes => Binary.invFbytes 64 bytes

/-- Every list of bytes is its own repetition of byte terminals. -/
theorem repBbyteSelf : (bytes : Binary.Bytes) →
    Binary.Rep Binary.Bbyte bytes.length bytes bytes
  | [] => .nil
  | byte :: bytes => by
      simpa using Binary.Rep.cons [byte] byte bytes bytes bytes.length
        (.mk byte) (repBbyteSelf bytes)

theorem invFbytes32_length {bytes : List Byte} {value : FN 32}
    (h : Binary.invFbytes 32 bytes = some value) : bytes.length = 4 := by
  simp only [Binary.invFbytes, signif, expon] at h
  split at h <;> simp_all

theorem invFbytes64_length {bytes : List Byte} {value : FN 64}
    (h : Binary.invFbytes 64 bytes = some value) : bytes.length = 8 := by
  simp only [Binary.invFbytes, signif, expon] at h
  split at h <;> simp_all

/-- The canonical byte decoder returns an inhabitant of the pinned numeric
syntax sort.  This is the executable half of AMD-016 for full-width loads. -/
theorem numOfBytes?_wf {type : NumType} {bytes : List Byte}
    {value : Num_ type} (h : numOfBytes? type bytes = some value) :
    ByteSolvedNumWfFor (authority := amendedExecutionAuthority) type value := by
  cases type with
  | i32 => trivial
  | i64 => trivial
  | f32 =>
      change FN.wf value = true
      apply Binary.Bf32.wf_of
      exact ⟨bytes, (invFbytes32_length h) ▸ repBbyteSelf bytes, h⟩
  | f64 =>
      change FN.wf value = true
      apply Binary.Bf64.wf_of
      exact ⟨bytes, (invFbytes64_length h) ▸ repBbyteSelf bytes, h⟩

/-- A concrete candidate for the literal carried by a numeric storage type.
The semantic byte equation is deliberately checked at each rule boundary;
this decoder therefore need not assume an inverse theorem for floating-point
encodings. -/
def storageLiteralCandidate? : (storage : StorageType) → List Byte →
    Option (Lit_ storage)
  | .val (.num type), bytes => numOfBytes? type bytes
  | .val (.vec .v128), bytes =>
      some (Numerics.ofNatWrap 128 (Binary.leNat bytes))
  | .val (.ref _), _ => none
  | .val .bot, _ => none
  | .pack type, bytes =>
      some (Numerics.ofNatWrap type.size (Binary.leNat bytes))

/-- Every canonical storage-literal candidate inhabits the pinned storage
syntax sort. -/
theorem storageLiteralCandidate?_wf {storage : StorageType} {bytes : List Byte}
    {literal : Lit_ storage}
    (h : storageLiteralCandidate? storage bytes = some literal) :
    ByteSolvedLiteralWfFor (authority := amendedExecutionAuthority)
      storage literal := by
  cases storage with
  | val type =>
      cases type with
      | num numberType =>
          change ByteSolvedNumWfFor
            (authority := amendedExecutionAuthority) numberType literal
          exact numOfBytes?_wf h
      | vec vectorType => trivial
      | ref referenceType => exact literal.elim
      | bot => exact literal.elim
  | pack packType => trivial

/-- Decode a prescribed number of fixed-width storage literals.  This is only
a candidate generator.  `arrayNewDataResults` checks every length, byte and
unpacking premise before constructing a relational step. -/
def storageLiteralCandidates (storage : StorageType) (width : Nat) :
    Nat → List Byte → Option (List (Lit_ storage))
  | 0, _ => some []
  | count + 1, bytes => do
      let literal ← storageLiteralCandidate? storage (slice bytes 0 width)
      let rest ← storageLiteralCandidates storage width count
        (bytes.drop width)
      pure (literal :: rest)

/-- Pointwise syntax-sort well-formedness of the repeated canonical storage
decoder. -/
theorem storageLiteralCandidates_wf (storage : StorageType) (width : Nat) :
    ∀ {count : Nat} {bytes : List Byte} {literals : List (Lit_ storage)},
      storageLiteralCandidates storage width count bytes = some literals →
      ∀ literal ∈ literals,
        ByteSolvedLiteralWfFor (authority := amendedExecutionAuthority)
          storage literal
  | 0, bytes, literals, h => by
      simp [storageLiteralCandidates] at h
      subst literals
      simp
  | count + 1, bytes, literals, h => by
      simp only [storageLiteralCandidates] at h
      cases hhead : storageLiteralCandidate? storage (slice bytes 0 width) with
      | none => simp [hhead] at h
      | some head =>
          cases htail : storageLiteralCandidates storage width count
              (bytes.drop width) with
          | none => simp [hhead, htail] at h
          | some tail =>
              simp [hhead, htail] at h
              subst literals
              intro literal hmem
              rcases List.mem_cons.1 hmem with rfl | hmem
              · exact storageLiteralCandidate?_wf hhead
              · exact storageLiteralCandidates_wf storage width htail literal hmem

/-- Execute the address case of `call_ref` after the canonical value prefix
has identified its final function reference. -/
def callRefFuncResults (z : State) (arguments : List Val)
    (address : FuncAddr) (typeUse : TypeUse) :
    List (StepAResult
      (z, vals arguments ++
        [.addrref (.funcAddr address), .plain (.callRef typeUse)])) :=
  match hfunc : z.funcinst[address]? with
  | none => []
  | some function =>
      match hcode : function.code with
      | .host _ => []
      | .func fn =>
          match hexpand : expandDt function.type with
          | none => []
          | some (.struct _) => []
          | some (.array _) => []
          | some (.func domain codomain) =>
              if hlength : domain.length = arguments.length then
                let frame : Frame :=
                  { locals := arguments.map some ++
                      fn.locals.map (fun localDecl => default_ localDecl.valtype)
                    mod := function.mod }
                [readResult (target :=
                    [.frame codomain.length frame
                      [.label codomain.length [] (plains fn.body.toList)]])
                  .callRefFunc (by
                    exact Step_read.callRefFunc
                      (authority := amendedExecutionAuthority)
                      (Nm := releasedNumerics) hfunc (.mk hexpand)
                      hlength rfl rfl hcode rfl)]
              else []

/-- Exact table lookup, including the trap branch. -/
def tableGetResults (z : State) (address : AddressLiteral) (x : TableIdx) :
    List (StepAResult
      (z, vals [address.toVal] ++ [.plain (.tableGet x)])) :=
  match htable : z.tableOf x with
  | none => []
  | some table =>
      if hoob : address.value.val ≥ table.refs.length then
        [readResult (target := [.trap]) .tableGetOob (by
          simpa [vals, AddressLiteral.toVal_toAdmin] using
            Step_read.tableGetOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htable hoob)]
      else
        match hvalue : table.refs[address.value.val]? with
        | none => []
        | some reference =>
            [readResult (target := [reference.toAdmin]) .tableGetVal (by
              simpa [vals, AddressLiteral.toVal_toAdmin] using
                Step_read.tableGetVal
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) htable hvalue)]

/-- Exact `table.size`, defined only when the table length is representable at
the table's declared address width, just as the relational rule requires. -/
def tableSizeResults (z : State) (x : TableIdx) :
    List (StepAResult (z, [.plain (.tableSize x)])) :=
  match htable : z.tableOf x with
  | none => []
  | some table =>
      match hsize : addressLiteralOfNat? table.type.addr table.refs.length with
      | none => []
      | some size =>
          [readResult (target := [constAddr table.type.addr size])
            .tableSize (by
              exact Step_read.tableSize
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) htable
                (addressLiteralOfNat?_eq_some_value hsize).symm rfl)]

/-- Exact expansion of `table.fill`, including its trap, zero and recursive
branches. -/
def tableFillResults (z : State) (type : AddrType) (index count : AddrLit type)
    (value : Val) (x : TableIdx) :
    List (StepAResult
      (z, vals [.num ⟨addrNumType type, addrLitToNum type index⟩, value,
          .num ⟨addrNumType type, addrLitToNum type count⟩] ++
        [.plain (.tableFill x)])) :=
  match htable : z.tableOf x with
  | none => []
  | some table =>
      if hoob : index.val + count.val > table.refs.length then
        [readResult (target := [.trap]) .tableFillOob (by
          simpa [vals, constAddr, Val.toAdmin] using
            Step_read.tableFillOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (z := z) (att := type)
              (i := index) (n := count) (v := value) htable hoob)]
      else if hzero : count.val = 0 then
        [readResult (target := []) .tableFillZero (by
          simpa [vals, constAddr, Val.toAdmin] using
            Step_read.tableFillZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (z := z) (att := type)
              (i := index) (n := count) (v := value)
              htable (by omega) hzero)]
      else
        match hnextIndex : addressLiteralOfNat? type (index.val + 1),
            hnextCount : addressLiteralOfNat? type (count.val - 1) with
        | some nextIndex, some nextCount =>
            [readResult (target :=
                [constAddr type index, value.toAdmin, .plain (.tableSet x),
                 constAddr type nextIndex, value.toAdmin,
                 constAddr type nextCount, .plain (.tableFill x)])
              .tableFillSucc (by
                apply Step_read.tableFillSucc
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) htable (by omega) hzero
                · exact addressLiteralOfNat?_eq_some_value hnextIndex
                · have hvalue :=
                    addressLiteralOfNat?_eq_some_value hnextCount
                  omega)]
        | _, _ => []

/-- Exact `table.copy` expansion at its three independently typed address
literals. -/
def tableCopyResults (z : State) (destination source count : AddressLiteral)
    (destinationTable sourceTable : TableIdx) :
    List (StepAResult
      (z, vals [destination.toVal, source.toVal, count.toVal] ++
        [.plain (.tableCopy destinationTable sourceTable)])) :=
  match hdestination : z.tableOf destinationTable,
      hsource : z.tableOf sourceTable with
  | some destinationInstance, some sourceInstance =>
      if hoob : destination.value.val + count.value.val >
            destinationInstance.refs.length ∨
          source.value.val + count.value.val > sourceInstance.refs.length then
        [readResult (target := [.trap]) .tableCopyOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.tableCopyOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hdestination hsource hoob)]
      else if hzero : count.value.val = 0 then
        [readResult (target := []) .tableCopyZero (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.tableCopyZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hdestination hsource (by omega) hzero)]
      else if horder : destination.value.val ≤ source.value.val then
        match hnextDestination : addressLiteralOfNat?
              destination.type (destination.value.val + 1),
            hnextSource : addressLiteralOfNat?
              source.type (source.value.val + 1),
            hnextCount : addressLiteralOfNat?
              count.type (count.value.val - 1) with
        | some nextDestination, some nextSource, some nextCount =>
            [readResult (target :=
                [destination.toAdmin, source.toAdmin,
                 .plain (.tableGet sourceTable),
                 .plain (.tableSet destinationTable),
                 constAddr destination.type nextDestination,
                 constAddr source.type nextSource,
                 constAddr count.type nextCount,
                 .plain (.tableCopy destinationTable sourceTable)])
              .tableCopyLe (by
                apply Step_read.tableCopyLe
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hdestination hsource (by omega)
                  hzero horder
                · exact addressLiteralOfNat?_eq_some_value hnextDestination
                · exact addressLiteralOfNat?_eq_some_value hnextSource
                · have hvalue := addressLiteralOfNat?_eq_some_value hnextCount
                  omega)]
        | _, _, _ => []
      else
        match hlastDestination : addressLiteralOfNat?
              destination.type
              (destination.value.val + count.value.val - 1),
            hlastSource : addressLiteralOfNat?
              source.type (source.value.val + count.value.val - 1),
            hnextCount : addressLiteralOfNat?
              count.type (count.value.val - 1) with
        | some lastDestination, some lastSource, some nextCount =>
            [readResult (target :=
                [constAddr destination.type lastDestination,
                 constAddr source.type lastSource,
                 .plain (.tableGet sourceTable),
                 .plain (.tableSet destinationTable),
                 destination.toAdmin, source.toAdmin,
                 constAddr count.type nextCount,
                 .plain (.tableCopy destinationTable sourceTable)])
              .tableCopyGt (by
                apply Step_read.tableCopyGt
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hdestination hsource (by omega)
                  hzero horder
                · have hvalue :=
                    addressLiteralOfNat?_eq_some_value hlastDestination
                  omega
                · have hvalue := addressLiteralOfNat?_eq_some_value hlastSource
                  omega
                · have hvalue := addressLiteralOfNat?_eq_some_value hnextCount
                  omega)]
        | _, _, _ => []
  | _, _ => []

/-- Exact `table.init` expansion. -/
def tableInitResults (z : State) (destination : AddressLiteral)
    (source count : U32) (tableIndex : TableIdx) (elemIndex : ElemIdx) :
    List (StepAResult
      (z, vals [destination.toVal, .num ⟨.i32, source⟩,
          .num ⟨.i32, count⟩] ++
        [.plain (.tableInit tableIndex elemIndex)])) :=
  match htable : z.tableOf tableIndex, helem : z.elemOf elemIndex with
  | some table, some elem =>
      if hoob : destination.value.val + count.val > table.refs.length ∨
          source.val + count.val > elem.refs.length then
        [readResult (target := [.trap]) .tableInitOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, constI32] using
            Step_read.tableInitOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htable helem hoob)]
      else if hzero : count.val = 0 then
        [readResult (target := []) .tableInitZero (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, constI32] using
            Step_read.tableInitZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htable helem (by omega) hzero)]
      else
        match href : elem.refs[source.val]?,
            hnextDestination : addressLiteralOfNat?
              destination.type (destination.value.val + 1),
            hnextSource : u32? (source.val + 1),
            hnextCount : u32? (count.val - 1) with
        | some reference, some nextDestination, some nextSource,
            some nextCount =>
            [readResult (target :=
                [destination.toAdmin, reference.toAdmin,
                 .plain (.tableSet tableIndex),
                 constAddr destination.type nextDestination,
                 constI32 nextSource, constI32 nextCount,
                 .plain (.tableInit tableIndex elemIndex)])
              .tableInitSucc (by
                apply Step_read.tableInitSucc
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) htable helem (by omega) hzero href
                · exact addressLiteralOfNat?_eq_some_value hnextDestination
                · exact addressLiteralOfNat?_eq_some_value
                    (type := .i32) hnextSource
                · have hvalue := addressLiteralOfNat?_eq_some_value
                    (type := .i32) hnextCount
                  omega)]
        | _, _, _, _ => []
  | _, _ => []

/-- Full-width scalar load. -/
def loadNumResults (z : State) (address : AddressLiteral) (type : NumType)
    (memoryIndex : MemIdx) (argument : MemArg) :
    List (StepAResult
      (z, vals [address.toVal] ++
        [.plain (.load type none memoryIndex argument)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : address.value.val + argument.offset.val + type.size / 8 >
          memory.bytes.length then
        [readResult (target := [.trap]) .loadNumOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.loadNumOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hoob)]
      else
        let bytes := slice memory.bytes
          (address.value.val + argument.offset.val) (type.size / 8)
        match hvalue : numOfBytes? type bytes with
        | none => []
        | some value =>
            if hbytes : releasedNumerics.nbytes_ type value = bytes then
              [readResult (target := [.plain (.const type value)])
                .loadNumVal (by
                  simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, bytes]
                    using Step_read.loadNumVal
                      (authority := amendedExecutionAuthority)
                      (Nm := releasedNumerics) hmemory hbytes
                      (numOfBytes?_wf hvalue))]
            else []

/-- Packed integer load. -/
def loadPackResults (z : State) (address : AddressLiteral) (input : Inn)
    (operation : LoadOp) (memoryIndex : MemIdx) (argument : MemArg) :
    List (StepAResult
      (z, vals [address.toVal] ++
        [.plain (.load input.toNumType (some operation) memoryIndex argument)])) :=
  let width := operation.sz.toNat
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : address.value.val + argument.offset.val + width / 8 >
          memory.bytes.length then
        [readResult (target := [.trap]) .loadPackOob (by
          rcases operation with ⟨size, extension⟩
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, width] using
            Step_read.loadPackOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hoob)]
      else
        let bytes := slice memory.bytes
          (address.value.val + argument.offset.val) (width / 8)
        let bits : IN width := Numerics.ofNatWrap width (Binary.leNat bytes)
        if hbytes : releasedNumerics.ibytes_ width bits = bytes then
          let value : InnLit input :=
            releasedNumerics.extend__ width input.size operation.sx bits
          [readResult (target := [constInn input value]) .loadPackVal (by
            rcases operation with ⟨size, extension⟩
            apply Step_read.loadPackVal
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory
            · simpa [bytes, width] using hbytes
            · rfl)]
        else []

/-- Whole-vector load. -/
def vloadResults (z : State) (address : AddressLiteral)
    (memoryIndex : MemIdx) (argument : MemArg) :
    List (StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 none memoryIndex argument)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : address.value.val + argument.offset.val +
          VecType.v128.size / 8 > memory.bytes.length then
        [readResult (target := [.trap]) .vloadOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.vloadOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hoob)]
      else
        let bytes := slice memory.bytes
          (address.value.val + argument.offset.val) (VecType.v128.size / 8)
        let value : V128Lit := Numerics.ofNatWrap 128 (Binary.leNat bytes)
        if hbytes : releasedNumerics.vbytes_ .v128 value = bytes then
          [readResult (target := [.plain (.vconst .v128 value)]) .vloadVal (by
            simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, bytes] using
              Step_read.vloadVal
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hmemory hbytes)]
        else []

/-- Every raw vector shape.  Execution later filters this finite syntax list by
the two shape equations carried by `vload-pack-val`. -/
def readVectorShapes : List Shape :=
  [ ⟨.pack .i8, .d1⟩, ⟨.pack .i8, .d2⟩, ⟨.pack .i8, .d4⟩,
    ⟨.pack .i8, .d8⟩, ⟨.pack .i8, .d16⟩,
    ⟨.pack .i16, .d1⟩, ⟨.pack .i16, .d2⟩, ⟨.pack .i16, .d4⟩,
    ⟨.pack .i16, .d8⟩, ⟨.pack .i16, .d16⟩,
    ⟨.num .i32, .d1⟩, ⟨.num .i32, .d2⟩, ⟨.num .i32, .d4⟩,
    ⟨.num .i32, .d8⟩, ⟨.num .i32, .d16⟩,
    ⟨.num .i64, .d1⟩, ⟨.num .i64, .d2⟩, ⟨.num .i64, .d4⟩,
    ⟨.num .i64, .d8⟩, ⟨.num .i64, .d16⟩,
    ⟨.num .f32, .d1⟩, ⟨.num .f32, .d2⟩, ⟨.num .f32, .d4⟩,
    ⟨.num .f32, .d8⟩, ⟨.num .f32, .d16⟩,
    ⟨.num .f64, .d1⟩, ⟨.num .f64, .d2⟩, ⟨.num .f64, .d4⟩,
    ⟨.num .f64, .d8⟩, ⟨.num .f64, .d16⟩ ]

theorem mem_readVectorShapes (shape : Shape) : shape ∈ readVectorShapes := by
  rcases shape with ⟨lane, dimension⟩
  cases lane with
  | pack packed => cases packed <;> cases dimension <;> decide
  | num number => cases number <;> cases dimension <;> decide

/-- Packed vector load.  The successful branch decodes each fixed-width chunk
canonically and tries every finite raw shape satisfying the relational side
conditions.  Failure and success are independent because the authority rules
can overlap for a zero chunk count. -/
def vloadPackResults (z : State) (address : AddressLiteral) (size : Sz)
    (count : Nat) (extension : Sx) (memoryIndex : MemIdx)
    (argument : MemArg) :
    List (StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 (some (.shape size count extension))
          memoryIndex argument)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      let failure :=
        if hoob : address.value.val + argument.offset.val +
            size.toNat * count / 8 > memory.bytes.length then
          [readResult (target := [.trap]) .vloadPackOob (by
            simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
              Step_read.vloadPackOob
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hmemory hoob)]
        else []
      let bitAt (m : Nat) : IN size.toNat :=
        Numerics.ofNatWrap size.toNat
          (Binary.leNat (slice memory.bytes
            (address.value.val + argument.offset.val +
              m * (size.toNat / 8))
            (size.toNat / 8)))
      let bits := (List.range count).map bitAt
      let success := readVectorShapes.flatMap fun shape =>
        if hsize : shape.lane.size = size.toNat * 2 then
          if hdim : shape.dim.toNat = count then
            if hbytes : ∀ m : Fin count,
                releasedNumerics.ibytes_ size.toNat (bitAt m.val) =
                  slice memory.bytes
                    (address.value.val + argument.offset.val +
                      m.val * (size.toNat / 8))
                    (size.toNat / 8) then
              match hlanes : bits.mapM (fun bit =>
                  inToLane shape.lane
                    (releasedNumerics.extend__ size.toNat shape.lane.size
                      extension bit)) with
              | none => []
              | some lanes =>
                  let value := releasedNumerics.inv_lanes_ shape lanes
                  [readResult (target := [.plain (.vconst .v128 value)])
                    .vloadPackVal (by
                      apply Step_read.vloadPackVal
                        (authority := amendedExecutionAuthority)
                        (Nm := releasedNumerics) hmemory hsize hdim
                      · change ((List.range count).map bitAt).length = count
                        simp
                      · intro m bit hbit
                        have hm : m < count := by
                          have := List.getElem?_eq_some_iff.mp hbit
                          rcases this with ⟨hmBits, _⟩
                          have hbitsLength : bits.length = count := by
                            change ((List.range count).map bitAt).length = count
                            simp
                          rw [hbitsLength] at hmBits
                          exact hmBits
                        have hcanonical : bits[m]? = some (bitAt m) := by
                          simp [bits, bitAt, hm]
                        have hbitEq := Option.some.inj
                          (hbit.symm.trans hcanonical)
                        subst bit
                        exact hbytes ⟨m, hm⟩
                      · exact hlanes
                      · rfl)]
            else []
          else []
        else []
      failure ++ success

/-- Vector splat load. -/
def vloadSplatResults (z : State) (address : AddressLiteral) (size : Sz)
    (memoryIndex : MemIdx) (argument : MemArg) :
    List (StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 (some (.splat size)) memoryIndex argument)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : address.value.val + argument.offset.val + size.toNat / 8 >
          memory.bytes.length then
        [readResult (target := [.trap]) .vloadSplatOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.vloadSplatOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hoob)]
      else
        let shape := storeLaneShape size
        let bytes := slice memory.bytes
          (address.value.val + argument.offset.val) (size.toNat / 8)
        let bits : IN shape.lane.size :=
          Numerics.ofNatWrap shape.lane.size (Binary.leNat bytes)
        if hbytes : releasedNumerics.ibytes_ shape.lane.size bits = bytes then
          match hlane : inToLane shape.lane bits with
          | none => []
          | some lane =>
              let value := releasedNumerics.inv_lanes_ shape
                (List.replicate shape.dim.toNat lane)
              [readResult (target := [.plain (.vconst .v128 value)])
                .vloadSplatVal (by
                  apply Step_read.vloadSplatVal
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) hmemory
                  · exact storeLaneShape_laneSize size
                  · exact storeLaneShape_dim size
                  · simpa [bytes] using hbytes
                  · exact hlane
                  · rfl)]
        else []

/-- Zero-extending vector load. -/
def vloadZeroResults (z : State) (address : AddressLiteral) (size : Sz)
    (memoryIndex : MemIdx) (argument : MemArg) :
    List (StepAResult
      (z, vals [address.toVal] ++
        [.plain (.vload .v128 (some (.zero size)) memoryIndex argument)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : address.value.val + argument.offset.val + size.toNat / 8 >
          memory.bytes.length then
        [readResult (target := [.trap]) .vloadZeroOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.vloadZeroOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hoob)]
      else
        let bytes := slice memory.bytes
          (address.value.val + argument.offset.val) (size.toNat / 8)
        let bits : IN size.toNat :=
          Numerics.ofNatWrap size.toNat (Binary.leNat bytes)
        if hbytes : releasedNumerics.ibytes_ size.toNat bits = bytes then
          let value : V128Lit :=
            releasedNumerics.extend__ size.toNat 128 .u bits
          [readResult (target := [.plain (.vconst .v128 value)])
            .vloadZeroVal (by
              apply Step_read.vloadZeroVal
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hmemory
              · simpa [bytes] using hbytes
              · rfl)]
        else []

/-- Lane-replacing vector load. -/
def vloadLaneResults (z : State) (address : AddressLiteral)
    (original : V128Lit) (size : Sz) (memoryIndex : MemIdx)
    (argument : MemArg) (laneIndex : LaneIdx) :
    List (StepAResult
      (z, vals [address.toVal, .vec ⟨.v128, original⟩] ++
        [.plain (.vloadLane .v128 size memoryIndex argument laneIndex)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : address.value.val + argument.offset.val + size.toNat / 8 >
          memory.bytes.length then
        [readResult (target := [.trap]) .vloadLaneOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.vloadLaneOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hoob)]
      else
        let shape := storeLaneShape size
        let bytes := slice memory.bytes
          (address.value.val + argument.offset.val) (size.toNat / 8)
        let bits : IN shape.lane.size :=
          Numerics.ofNatWrap shape.lane.size (Binary.leNat bytes)
        if hbytes : releasedNumerics.ibytes_ shape.lane.size bits = bytes then
          match hlane : inToLane shape.lane bits with
          | none => []
          | some lane =>
              match hset : setAt? (releasedNumerics.lanes_ shape original)
                  laneIndex.val lane with
              | none => []
              | some lanes =>
                  let value := releasedNumerics.inv_lanes_ shape lanes
                  [readResult (target := [.plain (.vconst .v128 value)])
                    .vloadLaneVal (by
                      apply Step_read.vloadLaneVal
                        (authority := amendedExecutionAuthority)
                        (Nm := releasedNumerics) hmemory
                      · exact storeLaneShape_laneSize size
                      · simpa [VecType.size] using storeLaneShape_dim size
                      · simpa [bytes] using hbytes
                      · exact hlane
                      · exact hset
                      · rfl)]
        else []

/-- Exact `memory.size`. -/
def memorySizeResults (z : State) (memoryIndex : MemIdx) :
    List (StepAResult (z, [.plain (.memorySize memoryIndex)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      let pages := memory.bytes.length / (64 * Ki)
      if hpages : pages * (64 * Ki) = memory.bytes.length then
        match hsize : addressLiteralOfNat? memory.type.addr pages with
        | none => []
        | some size =>
            [readResult (target := [constAddr memory.type.addr size])
              .memorySize (by
                apply Step_read.memorySize
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hmemory
                · rw [addressLiteralOfNat?_eq_some_value hsize]
                  exact hpages
                · rfl)]
      else []

/-- Exact expansion of `memory.fill`. -/
def memoryFillResults (z : State) (type : AddrType)
    (index count : AddrLit type) (value : Val) (memoryIndex : MemIdx) :
    List (StepAResult
      (z, vals [.num ⟨addrNumType type, addrLitToNum type index⟩, value,
          .num ⟨addrNumType type, addrLitToNum type count⟩] ++
        [.plain (.memoryFill memoryIndex)])) :=
  match hmemory : z.memOf memoryIndex with
  | none => []
  | some memory =>
      if hoob : index.val + count.val > memory.bytes.length then
        [readResult (target := [.trap]) .memoryFillOob (by
          simpa [vals, constAddr, Val.toAdmin] using
            Step_read.memoryFillOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (z := z) (att := type)
              (i := index) (n := count) (v := value) hmemory hoob)]
      else if hzero : count.val = 0 then
        [readResult (target := []) .memoryFillZero (by
          simpa [vals, constAddr, Val.toAdmin] using
            Step_read.memoryFillZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (z := z) (att := type)
              (i := index) (n := count) (v := value)
              hmemory (by omega) hzero)]
      else
        match hnextIndex : addressLiteralOfNat? type (index.val + 1),
            hnextCount : addressLiteralOfNat? type (count.val - 1) with
        | some nextIndex, some nextCount =>
            [readResult (target :=
                [constAddr type index, value.toAdmin,
                 .plain (.store .i32 (some ⟨.s8⟩) memoryIndex MemArg.zero),
                 constAddr type nextIndex, value.toAdmin,
                 constAddr type nextCount,
                 .plain (.memoryFill memoryIndex)])
              .memoryFillSucc (by
                apply Step_read.memoryFillSucc
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hmemory (by omega) hzero
                · exact addressLiteralOfNat?_eq_some_value hnextIndex
                · have hvalue := addressLiteralOfNat?_eq_some_value hnextCount
                  omega)]
        | _, _ => []

/-- Exact expansion of `memory.copy`. -/
def memoryCopyResults (z : State) (destination source count : AddressLiteral)
    (destinationMemory sourceMemory : MemIdx) :
    List (StepAResult
      (z, vals [destination.toVal, source.toVal, count.toVal] ++
        [.plain (.memoryCopy destinationMemory sourceMemory)])) :=
  match hdestination : z.memOf destinationMemory,
      hsource : z.memOf sourceMemory with
  | some destinationInstance, some sourceInstance =>
      if hoob : destination.value.val + count.value.val >
            destinationInstance.bytes.length ∨
          source.value.val + count.value.val > sourceInstance.bytes.length then
        [readResult (target := [.trap]) .memoryCopyOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.memoryCopyOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hdestination hsource hoob)]
      else if hzero : count.value.val = 0 then
        [readResult (target := []) .memoryCopyZero (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin] using
            Step_read.memoryCopyZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hdestination hsource (by omega) hzero)]
      else if horder : destination.value.val ≤ source.value.val then
        match hnextDestination : addressLiteralOfNat?
              destination.type (destination.value.val + 1),
            hnextSource : addressLiteralOfNat?
              source.type (source.value.val + 1),
            hnextCount : addressLiteralOfNat?
              count.type (count.value.val - 1) with
        | some nextDestination, some nextSource, some nextCount =>
            [readResult (target :=
                [destination.toAdmin, source.toAdmin,
                 .plain (.load .i32 (some ⟨.s8, .u⟩)
                    sourceMemory MemArg.zero),
                 .plain (.store .i32 (some ⟨.s8⟩)
                    destinationMemory MemArg.zero),
                 constAddr destination.type nextDestination,
                 constAddr source.type nextSource,
                 constAddr count.type nextCount,
                 .plain (.memoryCopy destinationMemory sourceMemory)])
              .memoryCopyLe (by
                apply Step_read.memoryCopyLe
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hdestination hsource (by omega)
                  hzero horder
                · exact addressLiteralOfNat?_eq_some_value hnextDestination
                · exact addressLiteralOfNat?_eq_some_value hnextSource
                · have hvalue := addressLiteralOfNat?_eq_some_value hnextCount
                  omega)]
        | _, _, _ => []
      else
        match hlastDestination : addressLiteralOfNat?
              destination.type
              (destination.value.val + count.value.val - 1),
            hlastSource : addressLiteralOfNat?
              source.type (source.value.val + count.value.val - 1),
            hnextCount : addressLiteralOfNat?
              count.type (count.value.val - 1) with
        | some lastDestination, some lastSource, some nextCount =>
            [readResult (target :=
                [constAddr destination.type lastDestination,
                 constAddr source.type lastSource,
                 .plain (.load .i32 (some ⟨.s8, .u⟩)
                    sourceMemory MemArg.zero),
                 .plain (.store .i32 (some ⟨.s8⟩)
                    destinationMemory MemArg.zero),
                 destination.toAdmin, source.toAdmin,
                 constAddr count.type nextCount,
                 .plain (.memoryCopy destinationMemory sourceMemory)])
              .memoryCopyGt (by
                apply Step_read.memoryCopyGt
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hdestination hsource (by omega)
                  hzero horder
                · have hvalue :=
                    addressLiteralOfNat?_eq_some_value hlastDestination
                  omega
                · have hvalue := addressLiteralOfNat?_eq_some_value hlastSource
                  omega
                · have hvalue := addressLiteralOfNat?_eq_some_value hnextCount
                  omega)]
        | _, _, _ => []
  | _, _ => []

/-- Exact expansion of `memory.init`. -/
def memoryInitResults (z : State) (destination : AddressLiteral)
    (source count : U32) (memoryIndex : MemIdx) (dataIndex : DataIdx) :
    List (StepAResult
      (z, vals [destination.toVal, .num ⟨.i32, source⟩,
          .num ⟨.i32, count⟩] ++
        [.plain (.memoryInit memoryIndex dataIndex)])) :=
  match hmemory : z.memOf memoryIndex, hdata : z.dataOf dataIndex with
  | some memory, some data =>
      if hoob : destination.value.val + count.val > memory.bytes.length ∨
          source.val + count.val > data.bytes.length then
        [readResult (target := [.trap]) .memoryInitOob (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, constI32] using
            Step_read.memoryInitOob
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hdata hoob)]
      else if hzero : count.val = 0 then
        [readResult (target := []) .memoryInitZero (by
          simpa [vals, AddressLiteral.toAdmin, Val.toAdmin, constI32] using
            Step_read.memoryInitZero
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) hmemory hdata (by omega) hzero)]
      else
        match hbyte : data.bytes[source.val]?,
            hbyteValue : u32? (data.bytes[source.val]?.getD default).val,
            hnextDestination : addressLiteralOfNat?
              destination.type (destination.value.val + 1),
            hnextSource : u32? (source.val + 1),
            hnextCount : u32? (count.val - 1) with
        | some byte, some byteValue, some nextDestination, some nextSource,
            some nextCount =>
            [readResult (target :=
                [destination.toAdmin, constI32 byteValue,
                 .plain (.store .i32 (some ⟨.s8⟩) memoryIndex MemArg.zero),
                 constAddr destination.type nextDestination,
                 constI32 nextSource, constI32 nextCount,
                 .plain (.memoryInit memoryIndex dataIndex)])
              .memoryInitSucc (by
                have hdefault : data.bytes[source.val]?.getD default = byte := by
                  simp [hbyte]
                apply Step_read.memoryInitSucc
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) hmemory hdata (by omega) hzero
                  hbyte
                · simpa [hdefault] using
                    addressLiteralOfNat?_eq_some_value
                      (type := .i32) hbyteValue
                · exact addressLiteralOfNat?_eq_some_value hnextDestination
                · exact addressLiteralOfNat?_eq_some_value
                    (type := .i32) hnextSource
                · have hvalue := addressLiteralOfNat?_eq_some_value
                    (type := .i32) hnextCount
                  omega)]
        | _, _, _, _, _ => []
  | _, _ => []

/-- Default struct construction. -/
def structNewDefaultResults (z : State) (typeIndex : TypeIdx) :
    List (StepAResult (z, [.plain (.structNewDefault typeIndex)])) :=
  match htype : z.typeOf typeIndex with
  | none => []
  | some type =>
      match hexpand : expandDt type with
      | some (.struct fields) =>
          match hdefaults : fields.toList.mapM
              (fun field => default_ (fieldStorage field).unpack) with
          | none => []
          | some values =>
              [readResult (target :=
                  vals values ++ [.plain (.structNew typeIndex)])
                .structNewDefault (by
                  exact Step_read.structNewDefault
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) htype (.mk hexpand) hdefaults)]
      | _ => []

/-- Struct field read. -/
def structGetResults (z : State) (reference : Ref) (extension : Option Sx)
    (typeIndex : TypeIdx) (fieldIndex : U32) :
    List (StepAResult
      (z, vals [.ref reference] ++
        [.plain (.structGet extension typeIndex fieldIndex)])) :=
  match reference with
  | .null heapType =>
      [readResult (target := [.trap]) .structGetNull (by
        simpa [vals, Val.toAdmin] using Step_read.structGetNull
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) (z := z) (ht := heapType)
          (sx := extension) (x := typeIndex) (i := fieldIndex))]
  | .addr (.structAddr address) =>
      match htype : z.typeOf typeIndex with
      | none => []
      | some type =>
          match hexpand : expandDt type with
          | some (.struct fields) =>
              match hstruct : z.structinst[address]?,
                  hfieldType : fields.toList[fieldIndex.val]? with
              | some struct, some fieldType =>
                  match hfield : struct.fields[fieldIndex.val]? with
                  | none => []
                  | some field =>
                      match hvalue : releasedNumerics.unpackfield_
                          (fieldStorage fieldType) extension field with
                      | none => []
                      | some value =>
                          [readResult (target := [value.toAdmin])
                            .structGetStruct (by
                              simpa [vals, Val.toAdmin] using
                                Step_read.structGetStruct
                                  (authority := amendedExecutionAuthority)
                                  (Nm := releasedNumerics) htype (.mk hexpand)
                                  hstruct hfieldType hfield hvalue)]
              | _, _ => []
          | _ => []
  | _ => []

/-- Default array construction. -/
def arrayNewDefaultResults (z : State) (count : U32) (typeIndex : TypeIdx) :
    List (StepAResult
      (z, vals [.num ⟨.i32, count⟩] ++
        [.plain (.arrayNewDefault typeIndex)])) :=
  match htype : z.typeOf typeIndex with
  | none => []
  | some type =>
      match hexpand : expandDt type with
      | some (.array fieldType) =>
          match hdefault : default_ (fieldStorage fieldType).unpack with
          | none => []
          | some value =>
              [readResult (target :=
                  vals (List.replicate count.val value) ++
                    [.plain (.arrayNewFixed typeIndex count)])
                .arrayNewDefault (by
                  simpa [vals, constI32, Val.toAdmin] using
                    Step_read.arrayNewDefault
                      (authority := amendedExecutionAuthority)
                      (Nm := releasedNumerics) htype (.mk hexpand) hdefault)]
      | _ => []

/-- Array construction from an element segment. -/
def arrayNewElemResults (z : State) (offset count : U32)
    (typeIndex : TypeIdx) (elemIndex : ElemIdx) :
    List (StepAResult
      (z, vals [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩] ++
        [.plain (.arrayNewElem typeIndex elemIndex)])) :=
  match helem : z.elemOf elemIndex with
  | none => []
  | some elem =>
      let failure :=
        if hoob : offset.val + count.val > elem.refs.length then
          [readResult (target := [.trap]) .arrayNewElemOob (by
            simpa [vals, constI32, Val.toAdmin] using
              Step_read.arrayNewElemOob
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) helem hoob)]
        else []
      let references := slice elem.refs offset.val count.val
      let success :=
        if hlength : references.length = count.val then
          [readResult (target :=
              vals (references.map Val.ref) ++
                [.plain (.arrayNewFixed typeIndex count)])
            .arrayNewElemAlloc (by
              apply Step_read.arrayNewElemAlloc
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) helem rfl hlength)]
        else []
      failure ++ success

/-- Array construction from a numeric data segment.  The generated literal
list is accepted only after all four relational premises (cardinality,
per-literal width, flattened bytes and unpacking) have been decided exactly. -/
def arrayNewDataResults (z : State) (offset count : U32)
    (typeIndex : TypeIdx) (dataIndex : DataIdx) :
    List (StepAResult
      (z, vals [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩] ++
        [.plain (.arrayNewData typeIndex dataIndex)])) :=
  match htype : z.typeOf typeIndex with
  | none => []
  | some type =>
      match hexpand : expandDt type with
      | some (.array fieldType) =>
          match hsize : zsize (fieldStorage fieldType),
              hdata : z.dataOf dataIndex with
          | some size, some data =>
              let failure :=
                if hoob : offset.val + count.val * size / 8 >
                    data.bytes.length then
                  [readResult (target := [.trap]) .arrayNewDataOob (by
                    simpa [vals, constI32, Val.toAdmin] using
                      Step_read.arrayNewDataOob
                        (authority := amendedExecutionAuthority)
                        (Nm := releasedNumerics) htype (.mk hexpand) hsize
                        hdata hoob)]
                else []
              let selected :=
                slice data.bytes offset.val (count.val * size / 8)
              let success :=
                match hcandidates : storageLiteralCandidates
                    (fieldStorage fieldType) (size / 8) count.val selected with
                | none => []
                | some literals =>
                    if hlength : literals.length = count.val then
                      if hwidth : ∀ literal ∈ literals,
                          (releasedNumerics.zbytes_
                            (fieldStorage fieldType) literal).length = size / 8
                      then
                        if hbytes : (literals.map (fun literal =>
                              releasedNumerics.zbytes_
                                (fieldStorage fieldType) literal)).flatten =
                            selected
                        then
                          match hinstructions : literals.mapM
                              (releasedNumerics.cunpackConst
                                (fieldStorage fieldType)) with
                          | none => []
                          | some instructions =>
                              [readResult (target :=
                                  plains instructions ++
                                    [.plain (.arrayNewFixed typeIndex count)])
                                .arrayNewDataNum (by
                                  apply Step_read.arrayNewDataNum
                                    (authority := amendedExecutionAuthority)
                                    (Nm := releasedNumerics) htype
                                    (.mk hexpand) hsize hdata hlength hwidth
                                  · exact hbytes
                                  · exact hinstructions
                                  · exact storageLiteralCandidates_wf
                                      (fieldStorage fieldType) (size / 8)
                                      hcandidates)]
                        else []
                      else []
                    else []
              failure ++ success
          | _, _ => []
      | _ => []

/-- Array field read. -/
def arrayGetResults (z : State) (reference : Ref) (index : U32)
    (extension : Option Sx) (typeIndex : TypeIdx) :
    List (StepAResult
      (z, vals [.ref reference, .num ⟨.i32, index⟩] ++
        [.plain (.arrayGet extension typeIndex)])) :=
  match reference with
  | .null heapType =>
      [readResult (target := [.trap]) .arrayGetNull (by
        simpa [vals, Val.toAdmin, constI32] using Step_read.arrayGetNull
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) (z := z) (ht := heapType)
          (i := index) (sx := extension) (x := typeIndex))]
  | .addr (.arrayAddr address) =>
      match harray : z.arrayinst[address]? with
      | none => []
      | some array =>
          if hoob : index.val ≥ array.fields.length then
            [readResult (target := [.trap]) .arrayGetOob (by
              simpa [vals, Val.toAdmin, constI32] using Step_read.arrayGetOob
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) harray hoob)]
          else
            match htype : z.typeOf typeIndex with
            | none => []
            | some type =>
                match hexpand : expandDt type with
                | some (.array fieldType) =>
                    match hfield : array.fields[index.val]? with
                    | none => []
                    | some field =>
                        match hvalue : releasedNumerics.unpackfield_
                            (fieldStorage fieldType) extension field with
                        | none => []
                        | some value =>
                            [readResult (target := [value.toAdmin])
                              .arrayGetArray (by
                                simpa [vals, Val.toAdmin, constI32] using
                                  Step_read.arrayGetArray
                                    (authority := amendedExecutionAuthority)
                                    (Nm := releasedNumerics) htype (.mk hexpand)
                                    harray hfield hvalue)]
                | _ => []
  | _ => []

/-- Array length. -/
def arrayLenResults (z : State) (reference : Ref) :
    List (StepAResult
      (z, vals [.ref reference] ++ [.plain .arrayLen])) :=
  match reference with
  | .null heapType =>
      [readResult (target := [.trap]) .arrayLenNull (by
        simpa [vals, Val.toAdmin] using Step_read.arrayLenNull
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) (z := z) (ht := heapType))]
  | .addr (.arrayAddr address) =>
      match harray : z.arrayinst[address]? with
      | none => []
      | some array =>
          match hlength : u32? array.fields.length with
          | none => []
          | some length =>
              [readResult (target := [constI32 length]) .arrayLenArray (by
                apply Step_read.arrayLenArray
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) harray
                exact addressLiteralOfNat?_eq_some_value
                  (type := .i32) hlength)]
  | _ => []

/-- Exact expansion of `array.fill`. -/
def arrayFillResults (z : State) (reference : Ref) (index : U32)
    (value : Val) (count : U32) (typeIndex : TypeIdx) :
    List (StepAResult
      (z, vals [.ref reference, .num ⟨.i32, index⟩, value,
          .num ⟨.i32, count⟩] ++ [.plain (.arrayFill typeIndex)])) :=
  match reference with
  | .null heapType =>
      [readResult (target := [.trap]) .arrayFillNull (by
        simpa [vals, Val.toAdmin, constI32] using Step_read.arrayFillNull
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) (z := z) (ht := heapType)
          (i := index) (n := count) (v := value) (x := typeIndex))]
  | .addr (.arrayAddr address) =>
      match harray : z.arrayinst[address]? with
      | none => []
      | some array =>
          if hoob : index.val + count.val > array.fields.length then
            [readResult (target := [.trap]) .arrayFillOob (by
              simpa [vals, Val.toAdmin, constI32] using Step_read.arrayFillOob
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) harray hoob)]
          else if hzero : count.val = 0 then
            [readResult (target := []) .arrayFillZero (by
              simpa [vals, Val.toAdmin, constI32] using Step_read.arrayFillZero
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) harray (by omega) hzero)]
          else
            match hnextIndex : u32? (index.val + 1),
                hnextCount : u32? (count.val - 1) with
            | some nextIndex, some nextCount =>
                [readResult (target :=
                    [.addrref (.arrayAddr address), constI32 index,
                     value.toAdmin, .plain (.arraySet typeIndex),
                     .addrref (.arrayAddr address), constI32 nextIndex,
                     value.toAdmin, constI32 nextCount,
                     .plain (.arrayFill typeIndex)])
                  .arrayFillSucc (by
                    apply Step_read.arrayFillSucc
                      (authority := amendedExecutionAuthority)
                      (Nm := releasedNumerics) harray (by omega) hzero
                    · exact addressLiteralOfNat?_eq_some_value
                        (type := .i32) hnextIndex
                    · have hvalue := addressLiteralOfNat?_eq_some_value
                        (type := .i32) hnextCount
                      omega)]
            | _, _ => []
  | _ => []

/-- Exact expansion of `array.copy`.  The two independently applicable OOB
rules are both retained when both bounds fail. -/
def arrayCopyResults (z : State) (destination : Ref) (destinationIndex : U32)
    (source : Ref) (sourceIndex count : U32)
    (destinationType sourceType : TypeIdx) :
    List (StepAResult
      (z, vals [.ref destination, .num ⟨.i32, destinationIndex⟩,
          .ref source, .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩] ++
        [.plain (.arrayCopy destinationType sourceType)])) :=
  let nullDestination :=
    match destination with
    | .null heapType =>
        [readResult (target := [.trap]) .arrayCopyNull1 (by
          simpa [vals, Val.toAdmin, constI32] using Step_read.arrayCopyNull1
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (ht₁ := heapType)
            (i₁ := destinationIndex) (i₂ := sourceIndex) (n := count)
            (r := source) (x₁ := destinationType) (x₂ := sourceType))]
    | _ => []
  let nullSource :=
    match source with
    | .null heapType =>
        [readResult (target := [.trap]) .arrayCopyNull2 (by
          simpa [vals, Val.toAdmin, constI32] using Step_read.arrayCopyNull2
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (ht₂ := heapType)
            (i₁ := destinationIndex) (i₂ := sourceIndex) (n := count)
            (r := destination) (x₁ := destinationType) (x₂ := sourceType))]
    | _ => []
  let independentDestinationOob :=
    match destination, source with
    | .addr (.arrayAddr destinationAddress),
        .addr (.arrayAddr sourceAddress) =>
        match hdestination : z.arrayinst[destinationAddress]? with
        | none => []
        | some destinationArray =>
            if hoob : destinationIndex.val + count.val >
                destinationArray.fields.length then
              [readResult (target := [.trap]) .arrayCopyOob1 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayCopyOob1
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) (a₂ := sourceAddress)
                    (i₂ := sourceIndex) (x₁ := destinationType)
                    (x₂ := sourceType) hdestination hoob)]
            else []
    | _, _ => []
  let independentSourceOob :=
    match destination, source with
    | .addr (.arrayAddr destinationAddress),
        .addr (.arrayAddr sourceAddress) =>
        match hsource : z.arrayinst[sourceAddress]? with
        | none => []
        | some sourceArray =>
            if hoob : sourceIndex.val + count.val >
                sourceArray.fields.length then
              [readResult (target := [.trap]) .arrayCopyOob2 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayCopyOob2
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) (a₁ := destinationAddress)
                    (i₁ := destinationIndex) (x₁ := destinationType)
                    (x₂ := sourceType) hsource hoob)]
            else []
    | _, _ => []
  nullDestination ++ nullSource ++ independentDestinationOob ++
    independentSourceOob ++
    match destination, source with
    | .addr (.arrayAddr destinationAddress), .addr (.arrayAddr sourceAddress) =>
        match hdestination : z.arrayinst[destinationAddress]?,
            hsource : z.arrayinst[sourceAddress]? with
        | some destinationArray, some sourceArray =>
            let destinationOob :=
              if hoob : destinationIndex.val + count.val >
                  destinationArray.fields.length then
                [readResult (target := [.trap]) .arrayCopyOob1 (by
                  simpa [vals, Val.toAdmin, constI32] using
                    Step_read.arrayCopyOob1
                      (authority := amendedExecutionAuthority)
                      (Nm := releasedNumerics) hdestination hoob)]
              else []
            let sourceOob :=
              if hoob : sourceIndex.val + count.val >
                  sourceArray.fields.length then
                [readResult (target := [.trap]) .arrayCopyOob2 (by
                  simpa [vals, Val.toAdmin, constI32] using
                    Step_read.arrayCopyOob2
                      (authority := amendedExecutionAuthority)
                      (Nm := releasedNumerics) hsource hoob)]
              else []
            destinationOob ++ sourceOob ++
              if hdestinationIn : ¬ (destinationIndex.val + count.val >
                    destinationArray.fields.length) then
                if hsourceIn : ¬ (sourceIndex.val + count.val >
                    sourceArray.fields.length) then
                  if hzero : count.val = 0 then
                    [readResult (target := []) .arrayCopyZero (by
                      simpa [vals, Val.toAdmin, constI32] using
                        Step_read.arrayCopyZero
                          (authority := amendedExecutionAuthority)
                          (Nm := releasedNumerics) hdestination hsource
                          hdestinationIn hsourceIn hzero)]
                  else
                    match htype : z.typeOf sourceType with
                    | none => []
                    | some type =>
                        match hexpand : expandDt type with
                        | some (.array fieldType) =>
                            match hextension : sx_ (fieldStorage fieldType) with
                            | none => []
                            | some extension =>
                                if horder : destinationIndex.val ≤
                                    sourceIndex.val then
                                  match hnextDestination : u32?
                                        (destinationIndex.val + 1),
                                      hnextSource : u32? (sourceIndex.val + 1),
                                      hnextCount : u32? (count.val - 1) with
                                  | some nextDestination, some nextSource,
                                      some nextCount =>
                                      [readResult (target :=
                                          [.addrref (.arrayAddr
                                              destinationAddress),
                                           constI32 destinationIndex,
                                           .addrref (.arrayAddr sourceAddress),
                                           constI32 sourceIndex,
                                           .plain (.arrayGet extension sourceType),
                                           .plain (.arraySet destinationType),
                                           .addrref (.arrayAddr
                                              destinationAddress),
                                           constI32 nextDestination,
                                           .addrref (.arrayAddr sourceAddress),
                                           constI32 nextSource,
                                           constI32 nextCount,
                                           .plain (.arrayCopy destinationType
                                              sourceType)])
                                        .arrayCopyLe (by
                                          apply Step_read.arrayCopyLe
                                            (authority :=
                                              amendedExecutionAuthority)
                                            (Nm := releasedNumerics)
                                            hdestination hsource hdestinationIn
                                            hsourceIn hzero htype (.mk hexpand)
                                            horder hextension
                                          · exact
                                              addressLiteralOfNat?_eq_some_value
                                                (type := .i32) hnextDestination
                                          · exact
                                              addressLiteralOfNat?_eq_some_value
                                                (type := .i32) hnextSource
                                          · have hvalue :=
                                              addressLiteralOfNat?_eq_some_value
                                                (type := .i32) hnextCount
                                            omega)]
                                  | _, _, _ => []
                                else
                                  match hlastDestination : u32?
                                        (destinationIndex.val + count.val - 1),
                                      hlastSource : u32?
                                        (sourceIndex.val + count.val - 1),
                                      hnextCount : u32? (count.val - 1) with
                                  | some lastDestination, some lastSource,
                                      some nextCount =>
                                      [readResult (target :=
                                          [.addrref (.arrayAddr
                                              destinationAddress),
                                           constI32 lastDestination,
                                           .addrref (.arrayAddr sourceAddress),
                                           constI32 lastSource,
                                           .plain (.arrayGet extension sourceType),
                                           .plain (.arraySet destinationType),
                                           .addrref (.arrayAddr
                                              destinationAddress),
                                           constI32 destinationIndex,
                                           .addrref (.arrayAddr sourceAddress),
                                           constI32 sourceIndex,
                                           constI32 nextCount,
                                           .plain (.arrayCopy destinationType
                                              sourceType)])
                                        .arrayCopyGt (by
                                          apply Step_read.arrayCopyGt
                                            (authority :=
                                              amendedExecutionAuthority)
                                            (Nm := releasedNumerics)
                                            hdestination hsource hdestinationIn
                                            hsourceIn hzero horder htype
                                            (.mk hexpand) hextension
                                          · have hvalue :=
                                              addressLiteralOfNat?_eq_some_value
                                                (type := .i32) hlastDestination
                                            omega
                                          · have hvalue :=
                                              addressLiteralOfNat?_eq_some_value
                                                (type := .i32) hlastSource
                                            omega
                                          · have hvalue :=
                                              addressLiteralOfNat?_eq_some_value
                                                (type := .i32) hnextCount
                                            omega)]
                                  | _, _, _ => []
                        | _ => []
                else []
              else []
        | _, _ => []
    | _, _ => []

/-- Exact expansion of `array.init_elem`. -/
def arrayInitElemResults (z : State) (arrayReference : Ref) (arrayIndex : U32)
    (elemIndex count : U32) (typeIndex : TypeIdx) (segmentIndex : ElemIdx) :
    List (StepAResult
      (z, vals [.ref arrayReference, .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, elemIndex⟩, .num ⟨.i32, count⟩] ++
        [.plain (.arrayInitElem typeIndex segmentIndex)])) :=
  let nullResult :=
    match arrayReference with
    | .null heapType =>
        [readResult (target := [.trap]) .arrayInitElemNull (by
          simpa [vals, Val.toAdmin, constI32] using Step_read.arrayInitElemNull
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (ht := heapType)
            (i := arrayIndex) (j := elemIndex) (n := count)
            (x := typeIndex) (y := segmentIndex))]
    | _ => []
  let independentArrayOob :=
    match arrayReference with
    | .addr (.arrayAddr address) =>
        match harray : z.arrayinst[address]? with
        | none => []
        | some array =>
            if hoob : arrayIndex.val + count.val > array.fields.length then
              [readResult (target := [.trap]) .arrayInitElemOob1 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayInitElemOob1
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) harray hoob)]
            else []
    | _ => []
  let independentElemOob :=
    match arrayReference with
    | .addr (.arrayAddr address) =>
        match helem : z.elemOf segmentIndex with
        | none => []
        | some elem =>
            if hoob : elemIndex.val + count.val > elem.refs.length then
              [readResult (target := [.trap]) .arrayInitElemOob2 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayInitElemOob2
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) (a := address)
                    (i := arrayIndex) (x := typeIndex) helem hoob)]
            else []
    | _ => []
  nullResult ++ independentArrayOob ++ independentElemOob ++
    match arrayReference with
    | .addr (.arrayAddr address) =>
      match harray : z.arrayinst[address]?, helem : z.elemOf segmentIndex with
      | some array, some elem =>
          let arrayOob :=
            if hoob : arrayIndex.val + count.val > array.fields.length then
              [readResult (target := [.trap]) .arrayInitElemOob1 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayInitElemOob1
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) harray hoob)]
            else []
          let elemOob :=
            if hoob : elemIndex.val + count.val > elem.refs.length then
              [readResult (target := [.trap]) .arrayInitElemOob2 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayInitElemOob2
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) helem hoob)]
            else []
          arrayOob ++ elemOob ++
            if harrayIn : ¬ (arrayIndex.val + count.val > array.fields.length) then
              if helemIn : ¬ (elemIndex.val + count.val > elem.refs.length) then
                if hzero : count.val = 0 then
                  [readResult (target := []) .arrayInitElemZero (by
                    simpa [vals, Val.toAdmin, constI32] using
                      Step_read.arrayInitElemZero
                        (authority := amendedExecutionAuthority)
                        (Nm := releasedNumerics) harray helem harrayIn
                        helemIn hzero)]
                else
                  match href : elem.refs[elemIndex.val]?,
                      hnextArray : u32? (arrayIndex.val + 1),
                      hnextElem : u32? (elemIndex.val + 1),
                      hnextCount : u32? (count.val - 1) with
                  | some reference, some nextArray, some nextElem,
                      some nextCount =>
                      [readResult (target :=
                          [.addrref (.arrayAddr address), constI32 arrayIndex,
                           reference.toAdmin, .plain (.arraySet typeIndex),
                           .addrref (.arrayAddr address), constI32 nextArray,
                           constI32 nextElem, constI32 nextCount,
                           .plain (.arrayInitElem typeIndex segmentIndex)])
                        .arrayInitElemSucc (by
                          apply Step_read.arrayInitElemSucc
                            (authority := amendedExecutionAuthority)
                            (Nm := releasedNumerics) harray helem harrayIn
                            helemIn hzero href
                          · exact addressLiteralOfNat?_eq_some_value
                              (type := .i32) hnextArray
                          · exact addressLiteralOfNat?_eq_some_value
                              (type := .i32) hnextElem
                          · have hvalue :=
                              addressLiteralOfNat?_eq_some_value
                                (type := .i32) hnextCount
                            omega)]
                  | _, _, _, _ => []
              else []
            else []
      | _, _ => []
    | _ => []

/-- Exact expansion of `array.init_data`.  Its two out-of-bounds rules are
independent in the source relation, so both candidates are retained when both
premises hold. -/
def arrayInitDataResults (z : State) (arrayReference : Ref) (arrayIndex : U32)
    (dataIndex count : U32) (typeIndex : TypeIdx) (segmentIndex : DataIdx) :
    List (StepAResult
      (z, vals [.ref arrayReference, .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩] ++
        [.plain (.arrayInitData typeIndex segmentIndex)])) :=
  match arrayReference with
  | .null heapType =>
      [readResult (target := [.trap]) .arrayInitDataNull (by
        simpa [vals, Val.toAdmin, constI32] using Step_read.arrayInitDataNull
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics) (z := z) (ht := heapType)
          (i := arrayIndex) (j := dataIndex) (n := count)
          (x := typeIndex) (y := segmentIndex))]
  | .addr (.arrayAddr address) =>
      let arrayOob :=
        match harray : z.arrayinst[address]? with
        | none => []
        | some array =>
            if hoob : arrayIndex.val + count.val > array.fields.length then
              [readResult (target := [.trap]) .arrayInitDataOob1 (by
                simpa [vals, Val.toAdmin, constI32] using
                  Step_read.arrayInitDataOob1
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) harray hoob)]
            else []
      let dataOob :=
        match htype : z.typeOf typeIndex with
        | none => []
        | some type =>
            match hexpand : expandDt type with
            | some (.array fieldType) =>
                match hsize : zsize (fieldStorage fieldType),
                    hdata : z.dataOf segmentIndex with
                | some size, some data =>
                    if hoob : dataIndex.val + count.val * size / 8 >
                        data.bytes.length then
                      [readResult (target := [.trap]) .arrayInitDataOob2 (by
                        simpa [vals, Val.toAdmin, constI32] using
                          Step_read.arrayInitDataOob2
                            (authority := amendedExecutionAuthority)
                            (Nm := releasedNumerics) htype (.mk hexpand)
                            hsize hdata hoob)]
                    else []
                | _, _ => []
            | _ => []
      arrayOob ++ dataOob ++
        match harray : z.arrayinst[address]?,
            htype : z.typeOf typeIndex with
        | some array, some type =>
            match hexpand : expandDt type with
            | some (.array fieldType) =>
                match hsize : zsize (fieldStorage fieldType),
                    hdata : z.dataOf segmentIndex with
                | some size, some data =>
                    if harrayIn : ¬ (arrayIndex.val + count.val >
                        array.fields.length) then
                      if hdataIn : ¬ (dataIndex.val + count.val * size / 8 >
                          data.bytes.length) then
                        if hzero : count.val = 0 then
                          [readResult (target := []) .arrayInitDataZero (by
                            simpa [vals, Val.toAdmin, constI32] using
                              Step_read.arrayInitDataZero
                                (authority := amendedExecutionAuthority)
                                (Nm := releasedNumerics) harray harrayIn
                                htype (.mk hexpand) hsize hdata hdataIn hzero)]
                        else
                          let selected :=
                            slice data.bytes dataIndex.val (size / 8)
                          match hliteral : storageLiteralCandidate?
                              (fieldStorage fieldType) selected with
                          | none => []
                          | some literal =>
                              if hbytes : releasedNumerics.zbytes_
                                  (fieldStorage fieldType) literal = selected
                              then
                                match hinstruction :
                                    releasedNumerics.cunpackConst
                                      (fieldStorage fieldType) literal with
                                | none => []
                                | some instruction =>
                                    match hnextArray :
                                          u32? (arrayIndex.val + 1),
                                        hnextData :
                                          u32? (dataIndex.val + size / 8),
                                        hnextCount : u32? (count.val - 1) with
                                    | some nextArray, some nextData,
                                        some nextCount =>
                                        [readResult (target :=
                                            [.addrref (.arrayAddr address),
                                             constI32 arrayIndex,
                                             .plain instruction,
                                             .plain (.arraySet typeIndex),
                                             .addrref (.arrayAddr address),
                                             constI32 nextArray,
                                             constI32 nextData,
                                             constI32 nextCount,
                                             .plain (.arrayInitData typeIndex
                                               segmentIndex)])
                                          .arrayInitDataNum (by
                                            apply Step_read.arrayInitDataNum
                                              (authority :=
                                                amendedExecutionAuthority)
                                              (Nm := releasedNumerics)
                                              harray harrayIn htype
                                              (.mk hexpand) hsize hdata
                                              hdataIn hzero hbytes hinstruction
                                              (storageLiteralCandidate?_wf
                                                hliteral)
                                            · exact
                                                addressLiteralOfNat?_eq_some_value
                                                  (type := .i32) hnextArray
                                            · exact
                                                addressLiteralOfNat?_eq_some_value
                                                  (type := .i32) hnextData
                                            · have hvalue :=
                                                addressLiteralOfNat?_eq_some_value
                                                  (type := .i32) hnextCount
                                              omega)]
                                    | _, _, _ => []
                              else []
                      else []
                    else []
                | _, _ => []
            | _ => []
        | _, _ => []
  | _ => []

/-- All store-reading outcomes of an exception at the head of a handler. -/
def throwRefHandlerResults (z : State) (arity : Nat) (catches : List Catch)
    (address : ExnAddr) :
    List (StepAResult
      (z, [.handler arity catches
        [.addrref (.exnAddr address), .plain .throwRef]])) :=
  match catches with
  | [] =>
      [readResult .throwRefHandlerEmpty
        (Step_read.throwRefHandlerEmpty
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics))]
  | .all label :: rest =>
      [readResult .throwRefHandlerCatchAll
        (Step_read.throwRefHandlerCatchAll
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics))]
  | .allRef label :: rest =>
      [readResult .throwRefHandlerCatchAllRef
        (Step_read.throwRefHandlerCatchAllRef
          (authority := amendedExecutionAuthority)
          (Nm := releasedNumerics))]
  | .tag tagIndex label :: rest =>
      match hexn : z.exninst[address]?,
          htag : z.tagaddr[tagIndex.val]? with
      | some exception, some tagAddress =>
          if heq : exception.tag = tagAddress then
            [readResult .throwRefHandlerCatch
              (Step_read.throwRefHandlerCatch
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hexn htag heq)]
          else
            [readResult .throwRefHandlerNext
              (Step_read.throwRefHandlerNext
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) (by
                  simpa [catchMatches, hexn, htag] using heq))]
      | none, _ =>
          [readResult .throwRefHandlerNext
            (Step_read.throwRefHandlerNext
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (by simp [catchMatches, hexn]))]
      | _, none =>
          [readResult .throwRefHandlerNext
            (Step_read.throwRefHandlerNext
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (by
                simp [catchMatches, hexn, htag]))]
  | .tagRef tagIndex label :: rest =>
      match hexn : z.exninst[address]?,
          htag : z.tagaddr[tagIndex.val]? with
      | some exception, some tagAddress =>
          if heq : exception.tag = tagAddress then
            [readResult .throwRefHandlerCatchRef
              (Step_read.throwRefHandlerCatchRef
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hexn htag heq)]
          else
            [readResult .throwRefHandlerNext
              (Step_read.throwRefHandlerNext
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) (by
                  simpa [catchMatches, hexn, htag] using heq))]
      | none, _ =>
          [readResult .throwRefHandlerNext
            (Step_read.throwRefHandlerNext
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (by simp [catchMatches, hexn]))]
      | _, none =>
          [readResult .throwRefHandlerNext
            (Step_read.throwRefHandlerNext
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (by
                simp [catchMatches, hexn, htag]))]

/-- Store-reading rules whose redex is a maximal value prefix followed by one
plain instruction.  Further arms are added by semantic family below; each arm
constructs the independent rule derivation at the point where it computes the
successor. -/
def instructionReadResults (z : State) (vs : List Val) (instruction : Instr) :
    List (StepAResult (z, vals vs ++ [.plain instruction])) :=
  match instruction with
  | .block blockType body =>
      match htype : blocktype_ z blockType with
      | none => []
      | some (domain, codomain) =>
          if hlength : domain.length = vs.length then
            [readResult .block
              (.block (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) htype hlength rfl rfl)]
          else []
  | .loop blockType body =>
      match htype : blocktype_ z blockType with
      | none => []
      | some (domain, codomain) =>
          if hlength : domain.length = vs.length then
            [readResult .loop
              (.loop (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) htype hlength rfl rfl)]
          else []
  | .tryTable blockType catches body =>
      match htype : blocktype_ z blockType with
      | none => []
      | some (domain, codomain) =>
          if hlength : domain.length = vs.length then
            [readResult .tryTable
              (.tryTable (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) htype hlength rfl rfl)]
          else []
  | .call x =>
      if hempty : vs = [] then
        match haddr : z.moduleinst.funcs[x.val]? with
        | none => []
        | some address =>
            match hfunc : z.funcinst[address]? with
            | none => []
            | some function =>
                [readResult (target :=
                    [.addrref (.funcAddr address),
                      .plain (.callRef (.defd function.type))]) .call (by
                  subst vs
                  simpa using Step_read.call
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) haddr hfunc)]
      else []
  | .returnCall x =>
      if hempty : vs = [] then
        match haddr : z.moduleinst.funcs[x.val]? with
        | none => []
        | some address =>
            match hfunc : z.funcinst[address]? with
            | none => []
            | some function =>
                [readResult (target :=
                    [.addrref (.funcAddr address),
                      .plain (.returnCallRef (.defd function.type))])
                  .returnCall (by
                  subst vs
                  simpa using Step_read.returnCall
                    (authority := amendedExecutionAuthority)
                    (Nm := releasedNumerics) haddr hfunc)]
      else []
  | .localGet x =>
      if hempty : vs = [] then
        match hlocal : z.localOf x with
        | some (some value) =>
            [readResult (target := [value.toAdmin]) .localGet (by
              subst vs
              simpa using Step_read.localGet
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hlocal)]
        | _ => []
      else []
  | .globalGet x =>
      if hempty : vs = [] then
        match hglobal : z.globalOf x with
        | none => []
        | some global =>
            [readResult (target := [global.value.toAdmin]) .globalGet (by
              subst vs
              simpa using Step_read.globalGet
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) hglobal)]
      else []
  | .refFunc x =>
      if hempty : vs = [] then
        match haddress : z.moduleinst.funcs[x.val]? with
        | none => []
        | some address =>
            [readResult (target := [.addrref (.funcAddr address)])
              .refFunc (by
                subst vs
                simpa using Step_read.refFunc
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) haddress)]
      else []
  | .structNewDefault typeIndex =>
      if hempty : vs = [] then
        (structNewDefaultResults z typeIndex).map fun result =>
          result.castSource (by
            apply Prod.ext
            · rfl
            · simp [hempty])
      else []
  | .structGet extension typeIndex fieldIndex =>
      match vs with
      | [.ref reference] =>
          structGetResults z reference extension typeIndex fieldIndex
      | _ => []
  | .arrayNewDefault typeIndex =>
      match vs with
      | [.num ⟨.i32, count⟩] => arrayNewDefaultResults z count typeIndex
      | _ => []
  | .arrayNewElem typeIndex elemIndex =>
      match vs with
      | [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩] =>
          arrayNewElemResults z offset count typeIndex elemIndex
      | _ => []
  | .arrayNewData typeIndex dataIndex =>
      match vs with
      | [.num ⟨.i32, offset⟩, .num ⟨.i32, count⟩] =>
          arrayNewDataResults z offset count typeIndex dataIndex
      | _ => []
  | .arrayGet extension typeIndex =>
      match vs with
      | [.ref reference, .num ⟨.i32, index⟩] =>
          arrayGetResults z reference index extension typeIndex
      | _ => []
  | .arrayLen =>
      match vs with
      | [.ref reference] => arrayLenResults z reference
      | _ => []
  | .arrayFill typeIndex =>
      match vs with
      | [.ref reference, .num ⟨.i32, index⟩, value,
          .num ⟨.i32, count⟩] =>
          arrayFillResults z reference index value count typeIndex
      | _ => []
  | .arrayCopy destinationType sourceType =>
      match vs with
      | [.ref destination, .num ⟨.i32, destinationIndex⟩,
          .ref source, .num ⟨.i32, sourceIndex⟩, .num ⟨.i32, count⟩] =>
          arrayCopyResults z destination destinationIndex source sourceIndex
            count destinationType sourceType
      | _ => []
  | .arrayInitElem typeIndex segmentIndex =>
      match vs with
      | [.ref reference, .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, elemIndex⟩, .num ⟨.i32, count⟩] =>
          arrayInitElemResults z reference arrayIndex elemIndex count typeIndex
            segmentIndex
      | _ => []
  | .arrayInitData typeIndex segmentIndex =>
      match vs with
      | [.ref reference, .num ⟨.i32, arrayIndex⟩,
          .num ⟨.i32, dataIndex⟩, .num ⟨.i32, count⟩] =>
          arrayInitDataResults z reference arrayIndex dataIndex count typeIndex
            segmentIndex
      | _ => []
  | .tableGet x =>
      match vs with
      | [value] =>
          match haddress : addressLiteral? value with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (tableGetResults z address x).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue, Inn.toNumType])
      | _ => []
  | .tableSize x =>
      if hempty : vs = [] then
        (tableSizeResults z x).map fun result =>
          result.castSource (by
            apply Prod.ext
            · rfl
            · simp [hempty])
      else []
  | .tableFill x =>
      match vs with
      | [.num ⟨.i32, index⟩, value, .num ⟨.i32, count⟩] =>
          tableFillResults z .i32 index count value x
      | [.num ⟨.i64, index⟩, value, .num ⟨.i64, count⟩] =>
          tableFillResults z .i64 index count value x
      | _ => []
  | .tableCopy destinationTable sourceTable =>
      match vs with
      | [destinationValue, sourceValue, countValue] =>
          match hdestination : addressLiteral? destinationValue,
              hsource : addressLiteral? sourceValue,
              hcount : addressLiteral? countValue with
          | some destination, some source, some count =>
              have hdestinationValue :=
                eq_toVal_of_addressLiteral?_eq_some hdestination
              have hsourceValue := eq_toVal_of_addressLiteral?_eq_some hsource
              have hcountValue := eq_toVal_of_addressLiteral?_eq_some hcount
              (tableCopyResults z destination source count destinationTable
                  sourceTable).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hdestinationValue, hsourceValue, hcountValue])
          | _, _, _ => []
      | _ => []
  | .tableInit tableIndex elemIndex =>
      match vs with
      | [destinationValue, .num ⟨.i32, source⟩, .num ⟨.i32, count⟩] =>
          match hdestination : addressLiteral? destinationValue with
          | none => []
          | some destination =>
              have hvalue :=
                eq_toVal_of_addressLiteral?_eq_some hdestination
              (tableInitResults z destination source count tableIndex
                  elemIndex).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue, Inn.toNumType])
      | _ => []
  | .load type none memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (loadNumResults z address type memoryIndex argument).map
                fun result => result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .load .i32 (some operation) memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (loadPackResults z address .i32 operation memoryIndex argument).map
                fun result => result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue, Inn.toNumType])
      | _ => []
  | .load .i64 (some operation) memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (loadPackResults z address .i64 operation memoryIndex argument).map
                fun result => result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue, Inn.toNumType])
      | _ => []
  | .load .f32 (some _) _ _ | .load .f64 (some _) _ _ => []
  | .vload .v128 none memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (vloadResults z address memoryIndex argument).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .vload .v128 (some (.splat size)) memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (vloadSplatResults z address size memoryIndex argument).map
                fun result => result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .vload .v128 (some (.zero size)) memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (vloadZeroResults z address size memoryIndex argument).map
                fun result => result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .vload .v128 (some (.shape size count extension)) memoryIndex argument =>
      match vs with
      | [addressValue] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (vloadPackResults z address size count extension memoryIndex
                  argument).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .vloadLane .v128 size memoryIndex argument laneIndex =>
      match vs with
      | [addressValue, .vec ⟨.v128, original⟩] =>
          match haddress : addressLiteral? addressValue with
          | none => []
          | some address =>
              have hvalue := eq_toVal_of_addressLiteral?_eq_some haddress
              (vloadLaneResults z address original size memoryIndex argument
                  laneIndex).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .memorySize memoryIndex =>
      if hempty : vs = [] then
        (memorySizeResults z memoryIndex).map fun result =>
          result.castSource (by
            apply Prod.ext
            · rfl
            · simp [hempty])
      else []
  | .memoryFill memoryIndex =>
      match vs with
      | [.num ⟨.i32, index⟩, value, .num ⟨.i32, count⟩] =>
          memoryFillResults z .i32 index count value memoryIndex
      | [.num ⟨.i64, index⟩, value, .num ⟨.i64, count⟩] =>
          memoryFillResults z .i64 index count value memoryIndex
      | _ => []
  | .memoryCopy destinationMemory sourceMemory =>
      match vs with
      | [destinationValue, sourceValue, countValue] =>
          match hdestination : addressLiteral? destinationValue,
              hsource : addressLiteral? sourceValue,
              hcount : addressLiteral? countValue with
          | some destination, some source, some count =>
              have hdestinationValue :=
                eq_toVal_of_addressLiteral?_eq_some hdestination
              have hsourceValue := eq_toVal_of_addressLiteral?_eq_some hsource
              have hcountValue := eq_toVal_of_addressLiteral?_eq_some hcount
              (memoryCopyResults z destination source count destinationMemory
                  sourceMemory).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hdestinationValue, hsourceValue, hcountValue])
          | _, _, _ => []
      | _ => []
  | .memoryInit memoryIndex dataIndex =>
      match vs with
      | [destinationValue, .num ⟨.i32, source⟩, .num ⟨.i32, count⟩] =>
          match hdestination : addressLiteral? destinationValue with
          | none => []
          | some destination =>
              have hvalue :=
                eq_toVal_of_addressLiteral?_eq_some hdestination
              (memoryInitResults z destination source count memoryIndex
                  dataIndex).map fun result =>
                result.castSource (by
                  apply Prod.ext
                  · rfl
                  · simp [hvalue])
      | _ => []
  | .callRef typeUse =>
      (match vs with
      | [.ref (.null heapType)] =>
          [readResult .callRefNull (by
            simpa [vals] using Step_read.callRefNull
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (z := z) (ht := heapType)
              (yy := typeUse))]
      | _ => []) ++
        match hlast : splitLastValue? vs with
        | none => []
        | some (arguments, .ref (.addr (.funcAddr address))) =>
            (callRefFuncResults z arguments address typeUse).map fun result =>
              result.castSource (by
                apply Prod.ext
                · rfl
                · have hvs : vs = arguments ++
                      [.ref (.addr (.funcAddr address))] :=
                    splitLastValue?_eq_append hlast
                  simp [hvs, vals, Val.toAdmin, List.map_append,
                    List.append_assoc])
        | some _ => []
  | .throwRef =>
      match vs with
      | [.ref (.null heapType)] =>
          [readResult .throwRefNull (by
            simpa [vals] using Step_read.throwRefNull
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (z := z) (ht := heapType))]
      | _ => []
  | _ => []

/-- Lift a canonical value-prefix result to the raw instruction sequence
reconstructed by `splitVals`. -/
def splitInstructionReadResults (z : State) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  let split := splitVals is
  match htail : split.2 with
  | [.plain instruction] =>
      (instructionReadResults z split.1 instruction).map fun result =>
        result.castSource (by
          apply Prod.ext
          · rfl
          · simpa [split, htail] using splitVals_append is)
  | _ => []

/-- `return_call_ref` escaping a label, recovered from the unique maximal
value prefix of the label body. -/
def returnCallRefLabelResults (z : State) (arity : Nat)
    (continuation body : List AdminInstr) :
    List (StepAResult (z, [.label arity continuation body])) :=
  let split := splitVals body
  match htail : split.2 with
  | .plain (.returnCallRef typeUse) :: suffix =>
      [(readResult .returnCallRefLabel
          (Step_read.returnCallRefLabel
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (k := arity)
            (cont := continuation) (vs := split.1) (yy := typeUse)
            (is := suffix)))
        |>.castSource (by
          apply Prod.ext
          · rfl
          · change
              [AdminInstr.label arity continuation
                (vals split.1 ++ [.plain (.returnCallRef typeUse)] ++ suffix)] =
                [AdminInstr.label arity continuation body]
            apply congrArg (fun inner =>
              [AdminInstr.label arity continuation inner])
            simpa [split, htail, List.append_assoc] using
              splitVals_append body)]
  | _ => []

/-- `return_call_ref` escaping a handler. -/
def returnCallRefHandlerResults (z : State) (arity : Nat)
    (catches : List Catch) (body : List AdminInstr) :
    List (StepAResult (z, [.handler arity catches body])) :=
  let split := splitVals body
  match htail : split.2 with
  | .plain (.returnCallRef typeUse) :: suffix =>
      [(readResult .returnCallRefHandler
          (Step_read.returnCallRefHandler
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (z := z) (k := arity)
            (cs := catches) (vs := split.1) (yy := typeUse)
            (is := suffix)))
        |>.castSource (by
          apply Prod.ext
          · rfl
          · change
              [AdminInstr.handler arity catches
                (vals split.1 ++ [.plain (.returnCallRef typeUse)] ++ suffix)] =
                [AdminInstr.handler arity catches body]
            apply congrArg (fun inner =>
              [AdminInstr.handler arity catches inner])
            simpa [split, htail, List.append_assoc] using
              splitVals_append body)]
  | _ => []

/-- The null branch of `return_call_ref` at its enclosing frame. -/
def returnCallRefFrameNullResults (z : State) (arity : Nat) (frame : Frame)
    (body : List AdminInstr) :
    List (StepAResult (z, [.frame arity frame body])) :=
  let split := splitVals body
  match htail : split.2 with
  | .plain (.returnCallRef typeUse) :: suffix =>
      match hlast : splitLastValue? split.1 with
      | some (initial, .ref (.null heapType)) =>
          [(readResult .returnCallRefFrameNull
              (Step_read.returnCallRefFrameNull
                (authority := amendedExecutionAuthority)
                (Nm := releasedNumerics) (z := z) (k := arity)
                (f := frame) (vs := initial) (ht := heapType)
                (yy := typeUse) (is := suffix)))
            |>.castSource (by
              apply Prod.ext
              · rfl
              · change
                  [AdminInstr.frame arity frame
                    (vals initial ++ [Ref.toAdmin (.null heapType),
                      .plain (.returnCallRef typeUse)] ++ suffix)] =
                    [AdminInstr.frame arity frame body]
                apply congrArg (fun inner =>
                  [AdminInstr.frame arity frame inner])
                have hprefix : split.1 =
                    initial ++ [.ref (.null heapType)] :=
                  splitLastValue?_eq_append hlast
                simpa [split, htail, hprefix, vals, Val.toAdmin,
                  List.map_append, List.append_assoc] using
                    splitVals_append body)]
      | _ => []
  | _ => []

/-- The function-address branch of `return_call_ref` at its enclosing frame.
The callee domain fixes the only suffix of the value prefix that can be passed
as arguments; an exact source equation is checked before the rule is emitted. -/
def returnCallRefFrameAddrResults (z : State) (arity : Nat) (frame : Frame)
    (body : List AdminInstr) :
    List (StepAResult (z, [.frame arity frame body])) :=
  let split := splitVals body
  match htail : split.2 with
  | .plain (.returnCallRef typeUse) :: suffix =>
      match hlast : splitLastValue? split.1 with
      | some (beforeAddress, .ref (.addr (.funcAddr address))) =>
          match hfunc : z.funcinst[address]? with
          | none => []
          | some function =>
              match hexpand : expandDt function.type with
              | some (.func domain codomain) =>
                  if hfits : domain.length ≤ beforeAddress.length then
                    let cut := beforeAddress.length - domain.length
                    let discarded := beforeAddress.take cut
                    let arguments := beforeAddress.drop cut
                    have harguments : arguments.length = domain.length := by
                      simp only [arguments, cut, List.length_drop]
                      omega
                    [(readResult .returnCallRefFrameAddr
                        (Step_read.returnCallRefFrameAddr
                          (authority := amendedExecutionAuthority)
                          (Nm := releasedNumerics) (z := z) (k := arity)
                          (f := frame) (vs' := discarded) (vs := arguments)
                          (a := address) (yy := typeUse) (is := suffix)
                          (fi := function) (t₁ := domain) (t₂ := codomain)
                          (n := domain.length) (m := codomain.length)
                          hfunc (.mk hexpand) rfl rfl harguments))
                      |>.castSource (by
                        apply Prod.ext
                        · rfl
                        · apply congrArg (fun inner =>
                            [AdminInstr.frame arity frame inner])
                          have hbefore : discarded ++ arguments =
                              beforeAddress := by
                            exact List.take_append_drop cut beforeAddress
                          have hprefix : split.1 =
                              beforeAddress ++
                                [.ref (.addr (.funcAddr address))] :=
                            splitLastValue?_eq_append hlast
                          have hprefix' : split.1 =
                              (discarded ++ arguments) ++
                                [.ref (.addr (.funcAddr address))] := by
                            rw [hbefore]
                            exact hprefix
                          simpa [split, htail, hprefix', vals, Val.toAdmin,
                            List.map_append, List.append_assoc] using
                              splitVals_append body)]
                  else []
              | _ => []
      | _ => []
  | _ => []

/-- Propagation of a thrown exception across surrounding instructions. -/
def throwRefInstrResults (z : State) (body : List AdminInstr) :
    List (StepAResult (z, body)) :=
  let split := splitVals body
  match htail : split.2 with
  | .plain .throwRef :: suffix =>
      match hlast : splitLastValue? split.1 with
      | some (initial, .ref (.addr (.exnAddr address))) =>
          if hnonempty : initial ≠ [] ∨ suffix ≠ [] then
            [(readResult .throwRefInstrs
                (Step_read.throwRefInstrs
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics) (z := z) (vs := initial)
                  (a := address) (is := suffix) hnonempty))
              |>.castSource (by
                apply Prod.ext
                · rfl
                · have hprefix : split.1 =
                      initial ++ [.ref (.addr (.exnAddr address))] :=
                    splitLastValue?_eq_append hlast
                  simpa [split, htail, hprefix, vals, Val.toAdmin,
                    List.map_append, List.append_assoc] using
                      splitVals_append body)]
          else []
      | _ => []
  | _ => []

/-- Store-reading rules whose source has an administrative wrapper. -/
def structuralReadResults (z : State) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  throwRefInstrResults z is ++
    match is with
    | [.label arity continuation body] =>
        returnCallRefLabelResults z arity continuation body ++
          match body with
          | [.addrref (.exnAddr address), .plain .throwRef] =>
              [readResult .throwRefLabel
                (Step_read.throwRefLabel
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics))]
          | _ => []
    | [.frame arity frame body] =>
        returnCallRefFrameNullResults z arity frame body ++
          returnCallRefFrameAddrResults z arity frame body ++
          match body with
          | [.addrref (.exnAddr address), .plain .throwRef] =>
              [readResult .throwRefFrame
                (Step_read.throwRefFrame
                  (authority := amendedExecutionAuthority)
                  (Nm := releasedNumerics))]
          | _ => []
    | [.handler arity catches body] =>
        returnCallRefHandlerResults z arity catches body ++
          match body with
          | [.addrref (.exnAddr address), .plain .throwRef] =>
              throwRefHandlerResults z arity catches address
          | _ => []
    | _ => []

/-- The indexed null rewrite is the sole read rule whose one-instruction
source is itself classified as a value by `splitVals`; it therefore sits
outside the value-prefix/instruction layer. -/
def elementaryReadResults (z : State) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  match is with
  | [.plain (.refNull (.use (.idx x)))] =>
      match htype : z.typeOf x with
      | none => []
      | some type =>
          [readResult (target :=
              [Ref.toAdmin (.null (.use (.defd type)))]) .refNullIdx
            (.refNullIdx (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) htype)]
  | _ => []

/-- Completeness of the executable reference matcher at one concrete state.
This premise is later derived from the validated allocation carried by a
public typed configuration; it is not asserted for arbitrary raw stores. -/
def RefMatchCompleteAt (fuel : Nat) (z : State) : Prop :=
  ∀ {reference : Ref} {target : RefType},
    (∃ actual : RefType, Ref_okA z.store reference actual ∧
      Reftype_subA Context.empty actual target) →
    refMatchesN fuel z.store reference target = true

/-- The eight reference-sensitive read rules.  Positive branches use matcher
soundness; negative branches use only the supplied typed-state completeness
proof.  The proof argument is erased, while the branch is selected by the
executable boolean. -/
def referenceInstructionReadResults (fuel : Nat) (z : State)
    (complete : RefMatchCompleteAt fuel z) (values : List Val)
    (instruction : Instr) :
    List (StepAResult (z, vals values ++ [.plain instruction])) :=
  match instruction, values with
  | .brOnCast label sourceType targetType, [.ref reference] =>
      let target := instRefType z.frame.mod targetType
      if hmatch : refMatchesN fuel z.store reference target = true then
        let witness := refMatchesN_sound hmatch
        [readResult .brOnCastSucceed (by
          obtain ⟨actual, href, hsub⟩ := witness
          simpa [vals, Val.toAdmin, target] using
            Step_read.brOnCastSucceed
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (l := label) (rt₁ := sourceType)
              href hsub)]
      else
        [readResult .brOnCastFail (by
          apply Step_read.brOnCastFail
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics)
          intro witness
          exact hmatch (complete (target := target) witness))]
  | .brOnCastFail label sourceType targetType, [.ref reference] =>
      let target := instRefType z.frame.mod targetType
      if hmatch : refMatchesN fuel z.store reference target = true then
        let witness := refMatchesN_sound hmatch
        [readResult .brOnCastFailSucceed (by
          obtain ⟨actual, href, hsub⟩ := witness
          simpa [vals, Val.toAdmin, target] using
            Step_read.brOnCastFailSucceed
              (authority := amendedExecutionAuthority)
              (Nm := releasedNumerics) (l := label) (rt₁ := sourceType)
              href hsub)]
      else
        [readResult .brOnCastFailFail (by
          apply Step_read.brOnCastFailFail
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics)
          intro witness
          exact hmatch (complete (target := target) witness))]
  | .refTest referenceType, [.ref reference] =>
      let target := instRefType z.frame.mod referenceType
      if hmatch : refMatchesN fuel z.store reference target = true then
        let witness := refMatchesN_sound hmatch
        [readResult (target := [constI32 ⟨1, by omega⟩]) .refTestTrue (by
          obtain ⟨actual, href, hsub⟩ := witness
          apply Step_read.refTestTrue
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (c := ⟨1, by omega⟩) href
          · simpa [target] using hsub
          · rfl)]
      else
        [readResult (target := [constI32 ⟨0, by omega⟩]) .refTestFalse (by
          apply Step_read.refTestFalse
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) (c := ⟨0, by omega⟩)
          · intro witness
            exact hmatch (complete (target := target) witness)
          · rfl)]
  | .refCast referenceType, [.ref reference] =>
      let target := instRefType z.frame.mod referenceType
      if hmatch : refMatchesN fuel z.store reference target = true then
        let witness := refMatchesN_sound hmatch
        [readResult .refCastSucceed (by
          obtain ⟨actual, href, hsub⟩ := witness
          apply Step_read.refCastSucceed
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics) href
          simpa [target] using hsub)]
      else
        [readResult .refCastFail (by
          apply Step_read.refCastFail
            (authority := amendedExecutionAuthority)
            (Nm := releasedNumerics)
          intro witness
          exact hmatch (complete (target := target) witness))]
  | _, _ => []

/-- Recover the reference-sensitive instruction redex under its maximal value
prefix. -/
def splitReferenceInstructionReadResults (fuel : Nat) (z : State)
    (complete : RefMatchCompleteAt fuel z) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  let split := splitVals is
  match htail : split.2 with
  | [.plain instruction] =>
      (referenceInstructionReadResults fuel z complete split.1 instruction).map
        fun result => result.castSource (by
          apply Prod.ext
          · rfl
          · simpa [split, htail] using splitVals_append is)
  | _ => []

/-- Proof erasure of the elementary store-reading layer. -/
def elementaryReadSuccessors (config : Config) : List (Event × Config) :=
  (elementaryReadResults config.1 config.2).map StepAResult.toPair

theorem mem_elementaryReadSuccessors_stepA {config : Config} {event : Event}
    {next : Config}
    (hmem : (event, next) ∈ elementaryReadSuccessors config) :
    StepA config event next := by
  rcases config with ⟨z, is⟩
  simp only [elementaryReadSuccessors, List.mem_map] at hmem
  obtain ⟨result, _, heq⟩ := hmem
  rcases result with ⟨emitted, successor, hstep⟩
  simp only [StepAResult.toPair, Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact hstep

/-- Every presently executable store-reading family, before proof erasure. -/
def readResults (z : State) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  elementaryReadResults z is ++ splitInstructionReadResults z is ++
    structuralReadResults z is

/-- Executable store-reading successors. -/
def readSuccessors (config : Config) : List (Event × Config) :=
  (readResults config.1 config.2).map StepAResult.toPair

/-- No successor emitted by the store-reading layer is invented. -/
theorem mem_readSuccessors_stepA {config : Config} {event : Event}
    {next : Config} (hmem : (event, next) ∈ readSuccessors config) :
    StepA config event next := by
  rcases config with ⟨z, is⟩
  simp only [readSuccessors, List.mem_map] at hmem
  obtain ⟨result, _, heq⟩ := hmem
  rcases result with ⟨emitted, successor, hstep⟩
  simp only [StepAResult.toPair, Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact hstep

/-- The full store-reading layer at a typed state, including the four
reference-sensitive instructions and both outcomes of each boolean test. -/
def readResultsOf (fuel : Nat) (z : State)
    (complete : RefMatchCompleteAt fuel z) (is : List AdminInstr) :
    List (StepAResult (z, is)) :=
  readResults z is ++ splitReferenceInstructionReadResults fuel z complete is

/-- Proof-erased store-reading successors at a state carrying matcher
completeness. -/
def readSuccessorsOf (fuel : Nat) (config : Config)
    (complete : RefMatchCompleteAt fuel config.1) : List (Event × Config) :=
  (readResultsOf fuel config.1 complete config.2).map StepAResult.toPair

/-- Every successor emitted by the typed store-reading layer is an amended
Core step. -/
theorem mem_readSuccessorsOf_stepA {fuel : Nat} {config : Config}
    (complete : RefMatchCompleteAt fuel config.1) {event : Event}
    {next : Config}
    (hmem : (event, next) ∈ readSuccessorsOf fuel config complete) :
    StepA config event next := by
  rcases config with ⟨z, is⟩
  simp only [readSuccessorsOf, List.mem_map] at hmem
  obtain ⟨result, _, heq⟩ := hmem
  rcases result with ⟨emitted, successor, hstep⟩
  simp only [StepAResult.toPair, Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact hstep

end WasmGemmGnaf.Wasm.Core.Exec
