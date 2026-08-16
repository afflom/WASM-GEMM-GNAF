import WasmGemmGnaf.Wasm.Core.RuntimeMatchComplete
import WasmGemmGnaf.Wasm.Core.EventExecution

/-! Reachable runtime configurations retain the allocated module type graph. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

mutual

@[simp] def AdminInstrTypesA (dts : List DefType) : AdminInstr → Prop
  | .plain _ | .addrref _ | .trap => True
  | .label _ continuation body =>
      AdminInstrsTypesA dts continuation ∧ AdminInstrsTypesA dts body
  | .frame _ frame body =>
      frame.mod.types = dts ∧ AdminInstrsTypesA dts body
  | .handler _ _ body => AdminInstrsTypesA dts body

@[simp] def AdminInstrsTypesA (dts : List DefType) : List AdminInstr → Prop
  | [] => True
  | instruction :: instructions =>
      AdminInstrTypesA dts instruction ∧ AdminInstrsTypesA dts instructions

end

@[simp] theorem adminInstrsTypesA_append (dts : List DefType)
    (left right : List AdminInstr) :
    AdminInstrsTypesA dts (left ++ right) ↔
      AdminInstrsTypesA dts left ∧ AdminInstrsTypesA dts right := by
  induction left with
  | nil => simp
  | cons instruction instructions ih =>
      simp only [List.cons_append, AdminInstrsTypesA, ih]
      constructor
      · rintro ⟨hinstruction, hinstructions, hright⟩
        exact ⟨⟨hinstruction, hinstructions⟩, hright⟩
      · rintro ⟨⟨hinstruction, hinstructions⟩, hright⟩
        exact ⟨hinstruction, hinstructions, hright⟩

@[simp] theorem adminInstrTypesA_val_toAdmin (dts : List DefType)
    (value : Val) : AdminInstrTypesA dts value.toAdmin := by
  cases value with
  | num number => simp [Val.toAdmin]
  | vec vector => simp [Val.toAdmin]
  | ref reference => cases reference <;> simp [Val.toAdmin]

@[simp] theorem adminInstrTypesA_ref_toAdmin (dts : List DefType)
    (reference : Ref) : AdminInstrTypesA dts reference.toAdmin := by
  cases reference <;> simp [Ref.toAdmin]

@[simp] theorem adminInstrTypesA_constAddr (dts : List DefType)
    (type : AddrType) (value : AddrLit type) :
    AdminInstrTypesA dts (constAddr type value) := by
  simp [constAddr]

@[simp] theorem adminInstrTypesA_constI32 (dts : List DefType)
    (value : U32) : AdminInstrTypesA dts (constI32 value) := by
  simp [constI32]

@[simp] theorem adminInstrTypesA_constInn (dts : List DefType)
    (type : Inn) (value : InnLit type) :
    AdminInstrTypesA dts (constInn type value) := by
  simp [constInn]

@[simp] theorem adminInstrsTypesA_vals (dts : List DefType)
    (values : List Val) : AdminInstrsTypesA dts (vals values) := by
  induction values with
  | nil => trivial
  | cons value values ih =>
      cases value with
      | num n => exact ⟨trivial, ih⟩
      | vec v => exact ⟨trivial, ih⟩
      | ref r => cases r <;> exact ⟨trivial, ih⟩

@[simp] theorem adminInstrsTypesA_plains (dts : List DefType)
    (instructions : List Instr) : AdminInstrsTypesA dts (plains instructions) := by
  induction instructions with
  | nil => trivial
  | cons instruction instructions ih => exact ⟨trivial, ih⟩

def ConfigTypeOriginsA (dts : List DefType) (config : Config) : Prop :=
  StoreTypeOriginsA config.1.store dts ∧
    config.1.frame.mod.types = dts ∧
    AdminInstrsTypesA dts config.2

theorem StoreTypeOriginsA.of_components {source target : Store}
    {dts : List DefType} (h : StoreTypeOriginsA source dts)
    (hstructs : target.structs = source.structs)
    (harrays : target.arrays = source.arrays)
    (hfuncs : target.funcs = source.funcs) :
    StoreTypeOriginsA target dts := by
  rcases h with ⟨hs, ha, hf⟩
  constructor
  · intro si hmem
    rw [hstructs] at hmem
    exact hs hmem
  constructor
  · intro ai hmem
    rw [harrays] at hmem
    exact ha hmem
  · intro fi hmem
    rw [hfuncs] at hmem
    exact hf hmem

theorem StoreTypeOriginsA.func_module_types {store : Store}
    {dts : List DefType} (h : StoreTypeOriginsA store dts)
    {address : FuncAddr} {function : FuncInst}
    (hlookup : store.funcs[address]? = some function) :
    function.mod.types = dts :=
  (h.2.2 (List.mem_of_getElem? hlookup)).2

private theorem struct_type_origin_of_mem_set
    {dts : List DefType} {structs : List StructInst}
    (horigin : ∀ {si : StructInst}, si ∈ structs →
      ∃ i : Nat, dts[i]? = some si.type)
    {address : Nat} {old : StructInst}
    (hlookup : structs[address]? = some old) {fields : List FieldVal}
    {candidate : StructInst}
    (hmember : candidate ∈ structs.set address { old with fields := fields }) :
    ∃ i : Nat, dts[i]? = some candidate.type := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmember
  rw [List.getElem_set] at heq
  by_cases haddress : address = j
  · simp [haddress] at heq
    have hcand : candidate.type = old.type := by rw [← heq]
    rw [hcand]
    exact horigin (List.mem_of_getElem? hlookup)
  · simp [haddress] at heq
    have hjold : j < structs.length := by simpa using hj
    have hsource : structs[j] = candidate := heq
    have hmem : structs[j] ∈ structs := List.getElem_mem hjold
    rw [hsource] at hmem
    exact horigin hmem

private theorem array_type_origin_of_mem_set
    {dts : List DefType} {arrays : List ArrayInst}
    (horigin : ∀ {ai : ArrayInst}, ai ∈ arrays →
      ∃ i : Nat, dts[i]? = some ai.type)
    {address : Nat} {old : ArrayInst}
    (hlookup : arrays[address]? = some old) {fields : List FieldVal}
    {candidate : ArrayInst}
    (hmember : candidate ∈ arrays.set address { old with fields := fields }) :
    ∃ i : Nat, dts[i]? = some candidate.type := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmember
  rw [List.getElem_set] at heq
  by_cases haddress : address = j
  · simp [haddress] at heq
    have hcand : candidate.type = old.type := by rw [← heq]
    rw [hcand]
    exact horigin (List.mem_of_getElem? hlookup)
  · simp [haddress] at heq
    have hjold : j < arrays.length := by simpa using hj
    have hsource : arrays[j] = candidate := heq
    have hmem : arrays[j] ∈ arrays := List.getElem_mem hjold
    rw [hsource] at hmem
    exact horigin hmem

theorem StoreTypeOriginsA.withStruct {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {address index : Nat}
    {field : FieldVal} (hupdate : z.withStruct address index field = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withStruct at hupdate
  cases hlookup : z.store.structs[address]? with
  | none => simp [hlookup] at hupdate
  | some old =>
      cases hfields : setAt? old.fields index field with
      | none => simp [hlookup, hfields] at hupdate
      | some fields =>
          cases hstructs : setAt? z.store.structs address
              { old with fields := fields } with
          | none => simp [hlookup, hfields, hstructs] at hupdate
          | some structs =>
              simp [hlookup, hfields, hstructs] at hupdate
              subst z'
              rcases horigin with ⟨hs, ha, hf⟩
              refine ⟨?_, ha, hf⟩
              intro candidate hmember
              unfold setAt? at hstructs
              split at hstructs
              · injection hstructs with heq
                subst structs
                exact struct_type_origin_of_mem_set hs hlookup hmember
              · contradiction

theorem StoreTypeOriginsA.withArray {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {address index : Nat}
    {field : FieldVal} (hupdate : z.withArray address index field = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withArray at hupdate
  cases hlookup : z.store.arrays[address]? with
  | none => simp [hlookup] at hupdate
  | some old =>
      cases hfields : setAt? old.fields index field with
      | none => simp [hlookup, hfields] at hupdate
      | some fields =>
          cases harrays : setAt? z.store.arrays address
              { old with fields := fields } with
          | none => simp [hlookup, hfields, harrays] at hupdate
          | some arrays =>
              simp [hlookup, hfields, harrays] at hupdate
              subst z'
              rcases horigin with ⟨hs, ha, hf⟩
              refine ⟨hs, ?_, hf⟩
              intro candidate hmember
              unfold setAt? at harrays
              split at harrays
              · injection harrays with heq
                subst arrays
                exact array_type_origin_of_mem_set ha hlookup hmember
              · contradiction

private theorem StoreTypeOriginsA.withLocal {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {index : LocalIdx}
    {value : Val} (hupdate : z.withLocal index value = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withLocal at hupdate
  cases hlocals : setAt? z.frame.locals index.val (some value) with
  | none => simp [hlocals] at hupdate
  | some locals =>
      simp [hlocals] at hupdate
      subst z'
      exact horigin

private theorem StoreTypeOriginsA.withGlobal {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {index : GlobalIdx}
    {value : Val} (hupdate : z.withGlobal index value = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withGlobal at hupdate
  cases haddress : z.frame.mod.globals[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hglobal : z.store.globals[address]? with
      | none => simp [haddress, hglobal] at hupdate
      | some global =>
          cases hglobals : setAt? z.store.globals address
              { global with value := value } with
          | none => simp [haddress, hglobal, hglobals] at hupdate
          | some globals =>
              simp [haddress, hglobal, hglobals] at hupdate
              subst z'
              exact horigin

private theorem StoreTypeOriginsA.withTable {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {index : TableIdx}
    {offset : Nat} {value : Ref}
    (hupdate : z.withTable index offset value = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withTable at hupdate
  cases haddress : z.frame.mod.tables[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases htable : z.store.tables[address]? with
      | none => simp [haddress, htable] at hupdate
      | some table =>
          cases hrefs : setAt? table.refs offset value with
          | none => simp [haddress, htable, hrefs] at hupdate
          | some refs =>
              cases htables : setAt? z.store.tables address
                  { table with refs := refs } with
              | none => simp [haddress, htable, hrefs, htables] at hupdate
              | some tables =>
                  simp [haddress, htable, hrefs, htables] at hupdate
                  subst z'
                  exact horigin

private theorem StoreTypeOriginsA.withTableInst {dts : List DefType}
    {z z' : State} (horigin : StoreTypeOriginsA z.store dts)
    {index : TableIdx} {value : TableInst}
    (hupdate : z.withTableInst index value = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withTableInst at hupdate
  cases haddress : z.frame.mod.tables[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases htables : setAt? z.store.tables address value with
      | none => simp [haddress, htables] at hupdate
      | some tables =>
          simp [haddress, htables] at hupdate
          subst z'
          exact horigin

private theorem StoreTypeOriginsA.withMem {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {index : MemIdx}
    {offset width : Nat} {bytes : List Byte}
    (hupdate : z.withMem index offset width bytes = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withMem at hupdate
  cases haddress : z.frame.mod.mems[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hmemory : z.store.mems[address]? with
      | none => simp [haddress, hmemory] at hupdate
      | some memory =>
          cases hbytes : spliceAt? memory.bytes offset width bytes with
          | none => simp [haddress, hmemory, hbytes] at hupdate
          | some resultBytes =>
              cases hmems : setAt? z.store.mems address
                  { memory with bytes := resultBytes } with
              | none =>
                  simp [haddress, hmemory, hbytes, hmems] at hupdate
              | some mems =>
                  simp [haddress, hmemory, hbytes, hmems] at hupdate
                  subst z'
                  exact horigin

private theorem StoreTypeOriginsA.withMemInst {dts : List DefType}
    {z z' : State} (horigin : StoreTypeOriginsA z.store dts)
    {index : MemIdx} {value : MemInst}
    (hupdate : z.withMemInst index value = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withMemInst at hupdate
  cases haddress : z.frame.mod.mems[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hmems : setAt? z.store.mems address value with
      | none => simp [haddress, hmems] at hupdate
      | some mems =>
          simp [haddress, hmems] at hupdate
          subst z'
          exact horigin

private theorem StoreTypeOriginsA.withElem {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {index : ElemIdx}
    {values : List Ref} (hupdate : z.withElem index values = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withElem at hupdate
  cases haddress : z.frame.mod.elems[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases helem : z.store.elems[address]? with
      | none => simp [haddress, helem] at hupdate
      | some elem =>
          cases helems : setAt? z.store.elems address
              { elem with refs := values } with
          | none => simp [haddress, helem, helems] at hupdate
          | some elems =>
              simp [haddress, helem, helems] at hupdate
              subst z'
              exact horigin

private theorem StoreTypeOriginsA.withData {dts : List DefType} {z z' : State}
    (horigin : StoreTypeOriginsA z.store dts) {index : DataIdx}
    {bytes : List Byte} (hupdate : z.withData index bytes = some z') :
    StoreTypeOriginsA z'.store dts := by
  unfold State.withData at hupdate
  cases haddress : z.frame.mod.datas[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hdata : z.store.datas[address]? with
      | none => simp [haddress, hdata] at hupdate
      | some data =>
          cases hdatas : setAt? z.store.datas address { data with bytes := bytes } with
          | none => simp [haddress, hdata, hdatas] at hupdate
          | some datas =>
              simp [haddress, hdata, hdatas] at hupdate
              subst z'
              exact horigin

private theorem StoreTypeOriginsA.addExnInst {dts : List DefType} {z : State}
    (horigin : StoreTypeOriginsA z.store dts) (values : List ExnInst) :
    StoreTypeOriginsA (z.addExnInst values).store dts := by
  exact horigin.of_components rfl rfl rfl

private theorem StoreTypeOriginsA.addStructInst {dts : List DefType}
    {z : State} (horigin : StoreTypeOriginsA z.store dts)
    (hstate : z.frame.mod.types = dts) {index : TypeIdx} {dt : DefType}
    (htype : z.typeOf index = some dt) {fields : List FieldVal} :
    StoreTypeOriginsA
      (z.addStructInst [{ type := dt, fields := fields }]).store dts := by
  rcases horigin with ⟨hstructs, harrays, hfuncs⟩
  refine ⟨?_, harrays, hfuncs⟩
  intro candidate hmember
  simp only [State.addStructInst, List.mem_append, List.mem_singleton] at hmember
  rcases hmember with hmember | rfl
  · exact hstructs hmember
  · unfold State.typeOf at htype
    rw [hstate] at htype
    exact ⟨index.val, htype⟩

private theorem StoreTypeOriginsA.addArrayInst {dts : List DefType}
    {z : State} (horigin : StoreTypeOriginsA z.store dts)
    (hstate : z.frame.mod.types = dts) {index : TypeIdx} {dt : DefType}
    (htype : z.typeOf index = some dt) {fields : List FieldVal} :
    StoreTypeOriginsA
      (z.addArrayInst [{ type := dt, fields := fields }]).store dts := by
  rcases horigin with ⟨hstructs, harrays, hfuncs⟩
  refine ⟨hstructs, ?_, hfuncs⟩
  intro candidate hmember
  simp only [State.addArrayInst, List.mem_append, List.mem_singleton] at hmember
  rcases hmember with hmember | rfl
  · exact harrays hmember
  · unfold State.typeOf at htype
    rw [hstate] at htype
    exact ⟨index.val, htype⟩

private theorem State.withLocal_frame {z z' : State} {index : LocalIdx}
    {value : Val} (hupdate : z.withLocal index value = some z') :
    z'.frame.mod.types = z.frame.mod.types := by
  unfold State.withLocal at hupdate
  cases hlocals : setAt? z.frame.locals index.val (some value) with
  | none => simp [hlocals] at hupdate
  | some locals =>
      simp [hlocals] at hupdate
      subst z'
      rfl

private theorem State.withGlobal_frame {z z' : State} {index : GlobalIdx}
    {value : Val} (hupdate : z.withGlobal index value = some z') :
    z'.frame = z.frame := by
  unfold State.withGlobal at hupdate
  cases haddress : z.frame.mod.globals[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hglobal : z.store.globals[address]? with
      | none => simp [haddress, hglobal] at hupdate
      | some global =>
          cases hglobals : setAt? z.store.globals address
              { global with value := value } with
          | none => simp [haddress, hglobal, hglobals] at hupdate
          | some globals =>
              simp [haddress, hglobal, hglobals] at hupdate
              subst z'
              rfl

private theorem State.withTable_frame {z z' : State} {index : TableIdx}
    {offset : Nat} {value : Ref}
    (hupdate : z.withTable index offset value = some z') :
    z'.frame = z.frame := by
  unfold State.withTable at hupdate
  cases haddress : z.frame.mod.tables[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases htable : z.store.tables[address]? with
      | none => simp [haddress, htable] at hupdate
      | some table =>
          cases hrefs : setAt? table.refs offset value with
          | none => simp [haddress, htable, hrefs] at hupdate
          | some refs =>
              cases htables : setAt? z.store.tables address
                  { table with refs := refs } with
              | none => simp [haddress, htable, hrefs, htables] at hupdate
              | some tables =>
                  simp [haddress, htable, hrefs, htables] at hupdate
                  subst z'
                  rfl

private theorem State.withTableInst_frame {z z' : State} {index : TableIdx}
    {value : TableInst} (hupdate : z.withTableInst index value = some z') :
    z'.frame = z.frame := by
  unfold State.withTableInst at hupdate
  cases haddress : z.frame.mod.tables[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases htables : setAt? z.store.tables address value with
      | none => simp [haddress, htables] at hupdate
      | some tables =>
          simp [haddress, htables] at hupdate
          subst z'
          rfl

private theorem State.withMem_frame {z z' : State} {index : MemIdx}
    {offset width : Nat} {bytes : List Byte}
    (hupdate : z.withMem index offset width bytes = some z') :
    z'.frame = z.frame := by
  unfold State.withMem at hupdate
  cases haddress : z.frame.mod.mems[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hmemory : z.store.mems[address]? with
      | none => simp [haddress, hmemory] at hupdate
      | some memory =>
          cases hbytes : spliceAt? memory.bytes offset width bytes with
          | none => simp [haddress, hmemory, hbytes] at hupdate
          | some resultBytes =>
              cases hmems : setAt? z.store.mems address
                  { memory with bytes := resultBytes } with
              | none => simp [haddress, hmemory, hbytes, hmems] at hupdate
              | some mems =>
                  simp [haddress, hmemory, hbytes, hmems] at hupdate
                  subst z'
                  rfl

private theorem State.withMemInst_frame {z z' : State} {index : MemIdx}
    {value : MemInst} (hupdate : z.withMemInst index value = some z') :
    z'.frame = z.frame := by
  unfold State.withMemInst at hupdate
  cases haddress : z.frame.mod.mems[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hmems : setAt? z.store.mems address value with
      | none => simp [haddress, hmems] at hupdate
      | some mems =>
          simp [haddress, hmems] at hupdate
          subst z'
          rfl

private theorem State.withElem_frame {z z' : State} {index : ElemIdx}
    {values : List Ref} (hupdate : z.withElem index values = some z') :
    z'.frame = z.frame := by
  unfold State.withElem at hupdate
  cases haddress : z.frame.mod.elems[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases helem : z.store.elems[address]? with
      | none => simp [haddress, helem] at hupdate
      | some elem =>
          cases helems : setAt? z.store.elems address
              { elem with refs := values } with
          | none => simp [haddress, helem, helems] at hupdate
          | some elems =>
              simp [haddress, helem, helems] at hupdate
              subst z'
              rfl

private theorem State.withData_frame {z z' : State} {index : DataIdx}
    {bytes : List Byte} (hupdate : z.withData index bytes = some z') :
    z'.frame = z.frame := by
  unfold State.withData at hupdate
  cases haddress : z.frame.mod.datas[index.val]? with
  | none => simp [haddress] at hupdate
  | some address =>
      cases hdata : z.store.datas[address]? with
      | none => simp [haddress, hdata] at hupdate
      | some data =>
          cases hdatas : setAt? z.store.datas address { data with bytes := bytes } with
          | none => simp [haddress, hdata, hdatas] at hupdate
          | some datas =>
              simp [haddress, hdata, hdatas] at hupdate
              subst z'
              rfl

private theorem State.withStruct_frame {z z' : State} {address index : Nat}
    {field : FieldVal} (hupdate : z.withStruct address index field = some z') :
    z'.frame = z.frame := by
  unfold State.withStruct at hupdate
  cases hstruct : z.store.structs[address]? with
  | none => simp [hstruct] at hupdate
  | some struct =>
      cases hfields : setAt? struct.fields index field with
      | none => simp [hstruct, hfields] at hupdate
      | some fields =>
          cases hstructs : setAt? z.store.structs address
              { struct with fields := fields } with
          | none => simp [hstruct, hfields, hstructs] at hupdate
          | some structs =>
              simp [hstruct, hfields, hstructs] at hupdate
              subst z'
              rfl

private theorem State.withArray_frame {z z' : State} {address index : Nat}
    {field : FieldVal} (hupdate : z.withArray address index field = some z') :
    z'.frame = z.frame := by
  unfold State.withArray at hupdate
  cases harray : z.store.arrays[address]? with
  | none => simp [harray] at hupdate
  | some array =>
      cases hfields : setAt? array.fields index field with
      | none => simp [harray, hfields] at hupdate
      | some fields =>
          cases harrays : setAt? z.store.arrays address
              { array with fields := fields } with
          | none => simp [harray, hfields, harrays] at hupdate
          | some arrays =>
              simp [harray, hfields, harrays] at hupdate
              subst z'
              rfl

theorem Step_pure.preserveAdminInstrsTypesA {Nm : Numerics}
    {source target : List AdminInstr} (step : Step_pure Nm source target)
    {dts : List DefType} (htyped : AdminInstrsTypesA dts source) :
    AdminInstrsTypesA dts target := by
  cases step <;> simp_all [AdminInstrsTypesA, AdminInstrTypesA]

theorem Step_readA.preserveAdminInstrsTypesA {z : State} {rule : ReadRule}
    {source target : List AdminInstr} (step : Step_readA z rule source target)
    {dts : List DefType} (hstate : z.frame.mod.types = dts)
    (hstore : StoreTypeOriginsA z.store dts)
    (htyped : AdminInstrsTypesA dts source) :
    AdminInstrsTypesA dts target := by
  cases step <;> simp_all [AdminInstrsTypesA, AdminInstrTypesA]
  apply hstore.func_module_types
  assumption

theorem StepA.preserveConfigTypeOriginsA {source target : Config}
    {event : Event} (step : StepA source event target) {dts : List DefType}
    (hsource : ConfigTypeOriginsA dts source) :
    ConfigTypeOriginsA dts target := by
  induction step with
  | pure hstep =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore, hframe,
        (mem_pureSuccessors_step_pure hstep).preserveAdminInstrsTypesA
          hinstructions⟩
  | read hstep =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore, hframe,
        hstep.preserveAdminInstrsTypesA hframe hstore hinstructions⟩
  | ctxtInstrs hstep hnon ih =>
      simp only [ConfigTypeOriginsA, adminInstrsTypesA_append,
        adminInstrsTypesA_vals, true_and] at hsource ⊢
      rcases hsource with ⟨hstore, hframe, hinstructions, hsuffix⟩
      rcases ih ⟨hstore, hframe, hinstructions⟩ with
        ⟨hstore', hframe', hinstructions'⟩
      exact ⟨hstore', hframe', hinstructions', hsuffix⟩
  | ctxtLabel hstep ih =>
      simp only [ConfigTypeOriginsA, AdminInstrsTypesA, AdminInstrTypesA,
        and_true] at hsource ⊢
      rcases hsource with ⟨hstore, hframe, hcontinuation, hinstructions⟩
      rcases ih ⟨hstore, hframe, hinstructions⟩ with
        ⟨hstore', hframe', hinstructions'⟩
      exact ⟨hstore', hframe', hcontinuation, hinstructions'⟩
  | ctxtFrame hstep ih =>
      simp only [ConfigTypeOriginsA, AdminInstrsTypesA, AdminInstrTypesA,
        and_true] at hsource ⊢
      rcases hsource with ⟨hstore, houter, hinner, hinstructions⟩
      rcases ih ⟨hstore, hinner, hinstructions⟩ with
        ⟨hstore', hinner', hinstructions'⟩
      exact ⟨hstore', houter, hinner', hinstructions'⟩
  | ctxtHandler hstep ih =>
      simp only [ConfigTypeOriginsA, AdminInstrsTypesA, AdminInstrTypesA,
        and_true] at hsource ⊢
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      rcases ih ⟨hstore, hframe, hinstructions⟩ with
        ⟨hstore', hframe', hinstructions'⟩
      exact ⟨hstore', hframe', hinstructions'⟩
  | trapHandler =>
      rcases hsource with ⟨hstore, hframe, _⟩
      exact ⟨hstore, hframe, by simp⟩
  | throw =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore.addExnInst _, hframe, by simp⟩
  | localSet hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withLocal hupdate, ?_, by simp⟩
      rw [State.withLocal_frame hupdate]
      exact hframe
  | globalSet hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withGlobal hupdate, ?_, by simp⟩
      rw [State.withGlobal_frame hupdate]
      exact hframe
  | tableSetOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | tableSetVal _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withTable hupdate, ?_, by simp⟩
      rw [State.withTable_frame hupdate]
      exact hframe
  | tableGrowSucceed _ _ hupdate _ =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withTableInst hupdate, ?_, by simp⟩
      rw [State.withTableInst_frame hupdate]
      exact hframe
  | tableGrowFail => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | elemDrop hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withElem hupdate, ?_, by simp⟩
      rw [State.withElem_frame hupdate]
      exact hframe
  | storeNumOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | storeNumVal _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rw [State.withMem_frame hupdate]
      exact hframe
  | storePackOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | storePackVal _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rw [State.withMem_frame hupdate]
      exact hframe
  | vstoreOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | vstoreVal _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rw [State.withMem_frame hupdate]
      exact hframe
  | vstoreLaneOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | vstoreLaneVal _ _ _ _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rw [State.withMem_frame hupdate]
      exact hframe
  | memoryGrowSucceed _ _ hupdate _ =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withMemInst hupdate, ?_, by simp⟩
      rw [State.withMemInst_frame hupdate]
      exact hframe
  | memoryGrowFail => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | dataDrop hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withData hupdate, ?_, by simp⟩
      rw [State.withData_frame hupdate]
      exact hframe
  | @structNew z vs index dt fields n address packed newStruct htype hexpand
      hfieldLength hvalueLength haddress hpack hinstance =>
      subst newStruct
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore.addStructInst hframe htype, hframe, by simp⟩
  | structSetNull => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | structSetStruct _ _ _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withStruct hupdate, ?_, by simp⟩
      rw [State.withStruct_frame hupdate]
      exact hframe
  | @arrayNewFixed z vs index n dt field address packed newArray htype hexpand
      hlength haddress hpack hinstance =>
      subst newArray
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore.addArrayInst hframe htype, hframe, by simp⟩
  | arraySetNull => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | arraySetOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | arraySetArray _ _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      refine ⟨hstore.withArray hupdate, ?_, by simp⟩
      rw [State.withArray_frame hupdate]
      exact hframe

/-! ## Empty-frame invocation compatibility -/

/-- Store-reading steps preserve nested module-type provenance without
requiring the active outer frame itself to be the allocated module.  This is
needed exactly once at the empty-frame `InvokeA` bootstrap. -/
theorem Step_readA.preserveAdminInstrsTypesA_from_store
    {z : State} {rule : ReadRule} {source target : List AdminInstr}
    (step : Step_readA z rule source target) {dts : List DefType}
    (hstore : StoreTypeOriginsA z.store dts)
    (htyped : AdminInstrsTypesA dts source) :
    AdminInstrsTypesA dts target := by
  cases step <;> simp_all [AdminInstrsTypesA, AdminInstrTypesA]
  apply hstore.func_module_types
  assumption

/-- Runtime-origin compatibility permits only the empty invocation bootstrap
frame or the allocated type vector belonging to the validated module.  Every
nested administrative frame still carries the allocated vector exactly. -/
def CompatibleConfigTypeOriginsA (dts : List DefType) (config : Config) : Prop :=
  StoreTypeOriginsA config.1.store dts ∧
    (config.1.frame.mod.types = [] ∨ config.1.frame.mod.types = dts) ∧
    AdminInstrsTypesA dts config.2

theorem ConfigTypeOriginsA.compatible {dts : List DefType} {config : Config}
    (h : ConfigTypeOriginsA dts config) :
    CompatibleConfigTypeOriginsA dts config :=
  ⟨h.1, Or.inr h.2.1, h.2.2⟩

/-- Replacing one memory instance cannot change the runtime origins of
functions, structs, or arrays. -/
theorem StoreTypeOriginsA.preserve_withMemInst {dts : List DefType}
    {source target : State} {index : MemIdx} {memory : MemInst}
    (h : StoreTypeOriginsA source.store dts)
    (hupdate : source.withMemInst index memory = some target) :
    StoreTypeOriginsA target.store dts :=
  h.withMemInst hupdate

/-- Splicing bytes into one memory instance cannot change the runtime origins
of functions, structs, or arrays. -/
theorem StoreTypeOriginsA.preserve_withMem {dts : List DefType}
    {source target : State} {index : MemIdx} {offset width : Nat}
    {bytes : List Byte} (h : StoreTypeOriginsA source.store dts)
    (hupdate : source.withMem index offset width bytes = some target) :
    StoreTypeOriginsA target.store dts :=
  h.withMem hupdate

/-- The only extra state admitted by `CompatibleConfigTypeOriginsA` is the
empty outer frame constructed by `InvokeA`.  Empty frames cannot resolve a
type index and therefore cannot allocate a struct or array of an unrelated
type. -/
theorem StepA.preserveCompatibleConfigTypeOriginsA
    {source target : Config} {event : Event} (step : StepA source event target)
    {dts : List DefType} (hsource : CompatibleConfigTypeOriginsA dts source) :
    CompatibleConfigTypeOriginsA dts target := by
  induction step with
  | pure hstep =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore, hframe,
        (mem_pureSuccessors_step_pure hstep).preserveAdminInstrsTypesA
          hinstructions⟩
  | read hstep =>
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      exact ⟨hstore, hframe,
        hstep.preserveAdminInstrsTypesA_from_store hstore hinstructions⟩
  | ctxtInstrs hstep hnon ih =>
      simp only [CompatibleConfigTypeOriginsA, adminInstrsTypesA_append,
        adminInstrsTypesA_vals, true_and] at hsource ⊢
      rcases hsource with ⟨hstore, hframe, hinstructions, hsuffix⟩
      rcases ih ⟨hstore, hframe, hinstructions⟩ with
        ⟨hstore', hframe', hinstructions'⟩
      exact ⟨hstore', hframe', hinstructions', hsuffix⟩
  | ctxtLabel hstep ih =>
      simp only [CompatibleConfigTypeOriginsA, AdminInstrsTypesA,
        AdminInstrTypesA, and_true] at hsource ⊢
      rcases hsource with ⟨hstore, hframe, hcontinuation, hinstructions⟩
      rcases ih ⟨hstore, hframe, hinstructions⟩ with
        ⟨hstore', hframe', hinstructions'⟩
      exact ⟨hstore', hframe', hcontinuation, hinstructions'⟩
  | ctxtFrame hstep ih =>
      simp only [CompatibleConfigTypeOriginsA, AdminInstrsTypesA,
        AdminInstrTypesA, and_true] at hsource ⊢
      rcases hsource with ⟨hstore, houter, hinner, hinstructions⟩
      rcases hstep.preserveConfigTypeOriginsA
          ⟨hstore, hinner, hinstructions⟩ with
        ⟨hstore', hinner', hinstructions'⟩
      exact ⟨hstore', houter, hinner', hinstructions'⟩
  | ctxtHandler hstep ih =>
      simp only [CompatibleConfigTypeOriginsA, AdminInstrsTypesA,
        AdminInstrTypesA, and_true] at hsource ⊢
      rcases hsource with ⟨hstore, hframe, hinstructions⟩
      rcases ih ⟨hstore, hframe, hinstructions⟩ with
        ⟨hstore', hframe', hinstructions'⟩
      exact ⟨hstore', hframe', hinstructions'⟩
  | trapHandler =>
      rcases hsource with ⟨hstore, hframe, _⟩
      exact ⟨hstore, hframe, by simp⟩
  | throw =>
      rcases hsource with ⟨hstore, hframe, _⟩
      exact ⟨hstore.addExnInst _, hframe, by simp⟩
  | localSet hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withLocal hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withLocal_frame hupdate]; exact hframe
      · right; rw [State.withLocal_frame hupdate]; exact hframe
  | globalSet hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withGlobal hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withGlobal_frame hupdate]; exact hframe
      · right; rw [State.withGlobal_frame hupdate]; exact hframe
  | tableSetOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | tableSetVal _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withTable hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withTable_frame hupdate]; exact hframe
      · right; rw [State.withTable_frame hupdate]; exact hframe
  | tableGrowSucceed _ _ hupdate _ =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withTableInst hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withTableInst_frame hupdate]; exact hframe
      · right; rw [State.withTableInst_frame hupdate]; exact hframe
  | tableGrowFail => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | elemDrop hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withElem hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withElem_frame hupdate]; exact hframe
      · right; rw [State.withElem_frame hupdate]; exact hframe
  | storeNumOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | storeNumVal _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withMem_frame hupdate]; exact hframe
      · right; rw [State.withMem_frame hupdate]; exact hframe
  | storePackOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | storePackVal _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withMem_frame hupdate]; exact hframe
      · right; rw [State.withMem_frame hupdate]; exact hframe
  | vstoreOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | vstoreVal _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withMem_frame hupdate]; exact hframe
      · right; rw [State.withMem_frame hupdate]; exact hframe
  | vstoreLaneOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | vstoreLaneVal _ _ _ _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withMem hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withMem_frame hupdate]; exact hframe
      · right; rw [State.withMem_frame hupdate]; exact hframe
  | memoryGrowSucceed _ _ hupdate _ =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withMemInst hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withMemInst_frame hupdate]; exact hframe
      · right; rw [State.withMemInst_frame hupdate]; exact hframe
  | memoryGrowFail => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | dataDrop hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withData hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withData_frame hupdate]; exact hframe
      · right; rw [State.withData_frame hupdate]; exact hframe
  | @structNew z vs index dt fields n address packed newStruct htype hexpand
      hfieldLength hvalueLength haddress hpack hinstance =>
      subst newStruct
      rcases hsource with ⟨hstore, hframe, _⟩
      rcases hframe with hframe | hframe
      · change z.frame.mod.types[index.val]? = some dt at htype
        rw [hframe] at htype
        simp at htype
      · exact ⟨hstore.addStructInst hframe htype, Or.inr hframe, by simp⟩
  | structSetNull => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | structSetStruct _ _ _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withStruct hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withStruct_frame hupdate]; exact hframe
      · right; rw [State.withStruct_frame hupdate]; exact hframe
  | @arrayNewFixed z vs index n dt field address packed newArray htype hexpand
      hlength haddress hpack hinstance =>
      subst newArray
      rcases hsource with ⟨hstore, hframe, _⟩
      rcases hframe with hframe | hframe
      · change z.frame.mod.types[index.val]? = some dt at htype
        rw [hframe] at htype
        simp at htype
      · exact ⟨hstore.addArrayInst hframe htype, Or.inr hframe, by simp⟩
  | arraySetNull => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | arraySetOob => exact ⟨hsource.1, hsource.2.1, by simp⟩
  | arraySetArray _ _ _ hupdate =>
      rcases hsource with ⟨hstore, hframe, _⟩
      refine ⟨hstore.withArray hupdate, ?_, by simp⟩
      rcases hframe with hframe | hframe
      · left; rw [State.withArray_frame hupdate]; exact hframe
      · right; rw [State.withArray_frame hupdate]; exact hframe

end WasmGemmGnaf.Wasm.Core.Exec
