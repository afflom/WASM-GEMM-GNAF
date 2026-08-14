/-
  The released event-labelled Core 3.0 machine.

  `Execution.lean` remains the single transcription of the pinned rules.  This
  file gives those derivations an independent rule-exact event alphabet and a
  first-class configuration carrier.  The labelled relation has one
  constructor per top-level `Step` rule; it is not defined by successor-list
  membership.  Erasure and completeness below prove that labels neither add
  nor remove an amended-authority, released-numerics transition.
-/
import WasmGemmGnaf.Wasm.Core.Successors

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace WasmGemmGnaf.Wasm.Core.Exec

/-- Syntactic instructions at the active administrative level.  Keeping these
operands in numeric/read events preserves shapes, lane counts, transfer widths,
memory/table indices and immediates needed by the exact cost table. -/
def sourcePlains (is : List AdminInstr) : List Instr :=
  is.filterMap fun
    | .plain i => some i
    | _ => none

/-- One exact Core rule event.  Context events retain the inner rule, and
state-writing rules retain every operand needed by the abstract cost table. -/
inductive Event where
  | pure (event : PureEvent) (operands : List Instr)
  | read (rule : ReadRule) (operands : List Instr)
  | ctxtInstrs (prefixValues suffixInstrs : Nat) (inner : Event)
  | ctxtLabel (arity : Nat) (inner : Event)
  | ctxtFrame (arity : Nat) (inner : Event)
  | throw (tag : TagIdx) (arity : Nat)
  | localSet (index : LocalIdx)
  | globalSet (index : GlobalIdx)
  | tableSetOob (table : TableIdx)
  | tableSetVal (table : TableIdx)
  | tableGrowSucceed (table : TableIdx) (delta oldSize newSize : Nat)
  | tableGrowFail (table : TableIdx) (delta : Nat)
  | elemDrop (elem : ElemIdx)
  | storeNumOob (mem : MemIdx) (bytes : Nat)
  | storeNumVal (mem : MemIdx) (bytes : Nat)
  | storePackOob (mem : MemIdx) (bytes : Nat)
  | storePackVal (mem : MemIdx) (bytes : Nat)
  | vstoreOob (mem : MemIdx) (bytes : Nat)
  | vstoreVal (mem : MemIdx) (bytes : Nat)
  | vstoreLaneOob (mem : MemIdx) (bytes : Nat)
  | vstoreLaneVal (mem : MemIdx) (bytes : Nat)
  | memoryGrowSucceed (mem : MemIdx) (delta oldPages newPages : Nat)
  | memoryGrowFail (mem : MemIdx) (delta : Nat)
  | dataDrop (data : DataIdx)
  | structNew (typeIdx : TypeIdx) (fields : Nat)
  | structSetNull (typeIdx : TypeIdx) (field : U32)
  | structSetStruct (typeIdx : TypeIdx) (field : U32)
  | arrayNewFixed (typeIdx : TypeIdx) (fields : Nat)
  | arraySetNull (typeIdx : TypeIdx)
  | arraySetOob (typeIdx : TypeIdx)
  | arraySetArray (typeIdx : TypeIdx)
  deriving DecidableEq, Repr, Inhabited

/-! ## Independent labelled one-step relation -/

/-- The sole public one-step relation: amended authority and released numerics
are fixed in its premises and every constructor determines its exact event. -/
inductive StepA : Config → Event → Config → Prop where
  | pure {z : State} {is is' : List AdminInstr}
      {pe : PureEvent} (h : (pe, is') ∈ pureSuccessors releasedNumerics is) :
      StepA (z, is) (.pure pe (sourcePlains is)) (z, is')
  | read {z : State} {rule : ReadRule} {is is' : List AdminInstr}
      (h : Step_readA z rule is is') :
      StepA (z, is) (.read rule (sourcePlains is)) (z, is')
  | ctxtInstrs {z z' : State} {vs : List Val} {is is' is₁ : List AdminInstr}
      {ev : Event} :
      StepA ⟨z, is⟩ ev ⟨z', is'⟩ → (vs ≠ [] ∨ is₁ ≠ []) →
      StepA ⟨z, vals vs ++ is ++ is₁⟩
        (.ctxtInstrs vs.length is₁.length ev)
        ⟨z', vals vs ++ is' ++ is₁⟩
  | ctxtLabel {z z' : State} {n : Nat} {cont is is' : List AdminInstr}
      {ev : Event} :
      StepA ⟨z, is⟩ ev ⟨z', is'⟩ →
      StepA ⟨z, [.label n cont is]⟩ (.ctxtLabel n ev)
        ⟨z', [.label n cont is']⟩
  | ctxtFrame {s s' : Store} {f f' f'' : Frame} {n : Nat}
      {is is' : List AdminInstr} {ev : Event} :
      StepA ⟨⟨s, f'⟩, is⟩ ev ⟨⟨s', f''⟩, is'⟩ →
      StepA ⟨⟨s, f⟩, [.frame n f' is]⟩ (.ctxtFrame n ev)
        ⟨⟨s', f⟩, [.frame n f'' is']⟩
  | throw {z : State} {vs : List Val} {x : TagIdx} {ti : TagInst}
      {dt : DefType} {t : ValTypes} {n : Nat} {a : ExnAddr} {ta : TagAddr}
      {ex : ExnInst} :
      z.tagOf x = some ti → asDefType ti.type = some dt →
      Expand dt (.func t .nil) → t.length = n → vs.length = n →
      a = z.exninst.length → z.tagaddr[x.val]? = some ta →
      ex = { tag := ta, fields := vs } →
      StepA ⟨z, vals vs ++ [.plain (.throw x)]⟩ (.throw x n)
        ⟨z.addExnInst [ex], [.addrref (.exnAddr a), .plain .throwRef]⟩
  | localSet {z z' : State} {v : Val} {x : LocalIdx} :
      z.withLocal x v = some z' →
      StepA ⟨z, [v.toAdmin, .plain (.localSet x)]⟩ (.localSet x) ⟨z', []⟩
  | globalSet {z z' : State} {v : Val} {x : GlobalIdx} :
      z.withGlobal x v = some z' →
      StepA ⟨z, [v.toAdmin, .plain (.globalSet x)]⟩ (.globalSet x) ⟨z', []⟩
  | tableSetOob {z : State} {att : AddrType} {i : AddrLit att} {r : Ref}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → i.val ≥ ti.refs.length →
      StepA ⟨z, [constAddr att i, r.toAdmin, .plain (.tableSet x)]⟩
        (.tableSetOob x) ⟨z, [.trap]⟩
  | tableSetVal {z z' : State} {att : AddrType} {i : AddrLit att} {r : Ref}
      {x : TableIdx} {ti : TableInst} :
      z.tableOf x = some ti → i.val < ti.refs.length →
      z.withTable x i.val r = some z' →
      StepA ⟨z, [constAddr att i, r.toAdmin, .plain (.tableSet x)]⟩
        (.tableSetVal x) ⟨z', []⟩
  | tableGrowSucceed {z z' : State} {att : AddrType} {n sz : AddrLit att}
      {r : Ref} {x : TableIdx} {ti ti' : TableInst} :
      z.tableOf x = some ti → growTable ti n.val r = some ti' →
      z.withTableInst x ti' = some z' → sz.val = ti.refs.length →
      StepA ⟨z, [r.toAdmin, constAddr att n, .plain (.tableGrow x)]⟩
        (.tableGrowSucceed x n.val ti.refs.length ti'.refs.length)
        ⟨z', [constAddr att sz]⟩
  | tableGrowFail {z : State} {att : AddrType} {n : AddrLit att} {r : Ref}
      {x : TableIdx} {e : AddrLit att} :
      e = Numerics.inv_signed_ (addrSize att) (-1) →
      StepA ⟨z, [r.toAdmin, constAddr att n, .plain (.tableGrow x)]⟩
        (.tableGrowFail x n.val) ⟨z, [constAddr att e]⟩
  | elemDrop {z z' : State} {x : ElemIdx} :
      z.withElem x [] = some z' →
      StepA ⟨z, [.plain (.elemDrop x)]⟩ (.elemDrop x) ⟨z', []⟩
  | storeNumOob {z : State} {att : AddrType} {i : AddrLit att}
      {nt : NumType} {c : Num_ nt} {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + nt.size / 8 > mi.bytes.length →
      StepA ⟨z, [constAddr att i, .plain (.const nt c),
          .plain (.store nt none x ao)]⟩
        (.storeNumOob x (nt.size / 8)) ⟨z, [.trap]⟩
  | storeNumVal {z z' : State} {att : AddrType} {i : AddrLit att}
      {nt : NumType} {c : Num_ nt} {x : MemIdx} {ao : MemArg}
      {bs : List Byte} :
      bs = releasedNumerics.nbytes_ nt c →
      z.withMem x (i.val + ao.offset.val) (nt.size / 8) bs = some z' →
      StepA ⟨z, [constAddr att i, .plain (.const nt c),
          .plain (.store nt none x ao)]⟩
        (.storeNumVal x (nt.size / 8)) ⟨z', []⟩
  | storePackOob {z : State} {att : AddrType} {i : AddrLit att} {inn : Inn}
      {c : InnLit inn} {sz : Sz} {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + sz.toNat / 8 > mi.bytes.length →
      StepA ⟨z, [constAddr att i, constInn inn c,
          .plain (.store inn.toNumType (some ⟨sz⟩) x ao)]⟩
        (.storePackOob x (sz.toNat / 8)) ⟨z, [.trap]⟩
  | storePackVal {z z' : State} {att : AddrType} {i : AddrLit att} {inn : Inn}
      {c : InnLit inn} {sz : Sz} {x : MemIdx} {ao : MemArg}
      {bs : List Byte} :
      bs = releasedNumerics.ibytes_ sz.toNat
        (releasedNumerics.wrap__ inn.size sz.toNat c) →
      z.withMem x (i.val + ao.offset.val) (sz.toNat / 8) bs = some z' →
      StepA ⟨z, [constAddr att i, constInn inn c,
          .plain (.store inn.toNumType (some ⟨sz⟩) x ao)]⟩
        (.storePackVal x (sz.toNat / 8)) ⟨z', []⟩
  | vstoreOob {z : State} {att : AddrType} {i : AddrLit att} {c : V128Lit}
      {x : MemIdx} {ao : MemArg} {mi : MemInst} :
      z.memOf x = some mi →
      i.val + ao.offset.val + VecType.v128.size / 8 > mi.bytes.length →
      StepA ⟨z, [constAddr att i, .plain (.vconst .v128 c),
          .plain (.vstore .v128 x ao)]⟩
        (.vstoreOob x (VecType.v128.size / 8)) ⟨z, [.trap]⟩
  | vstoreVal {z z' : State} {att : AddrType} {i : AddrLit att} {c : V128Lit}
      {x : MemIdx} {ao : MemArg} {bs : List Byte} :
      bs = releasedNumerics.vbytes_ .v128 c →
      z.withMem x (i.val + ao.offset.val) (VecType.v128.size / 8) bs = some z' →
      StepA ⟨z, [constAddr att i, .plain (.vconst .v128 c),
          .plain (.vstore .v128 x ao)]⟩
        (.vstoreVal x (VecType.v128.size / 8)) ⟨z', []⟩
  | vstoreLaneOob {z : State} {att : AddrType} {i : AddrLit att}
      {c : V128Lit} {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx}
      {mi : MemInst} :
      z.memOf x = some mi → i.val + ao.offset.val + sz.toNat > mi.bytes.length →
      StepA ⟨z, [constAddr att i, .plain (.vconst .v128 c),
          .plain (.vstoreLane .v128 sz x ao j)]⟩
        (.vstoreLaneOob x (sz.toNat / 8)) ⟨z, [.trap]⟩
  | vstoreLaneVal {z z' : State} {att : AddrType} {i : AddrLit att}
      {c : V128Lit} {sz : Sz} {x : MemIdx} {ao : MemArg} {j : LaneIdx}
      {sh : Shape} {lv : Lane_ sh.lane} {k : IN sh.lane.size}
      {bs : List Byte} :
      sh.lane.size = sz.toNat → sh.dim.toNat = 128 / sz.toNat →
      (releasedNumerics.lanes_ sh c)[j.val]? = some lv →
      laneToIN sh.lane lv = some k →
      bs = releasedNumerics.ibytes_ sh.lane.size k →
      z.withMem x (i.val + ao.offset.val) (sz.toNat / 8) bs = some z' →
      StepA ⟨z, [constAddr att i, .plain (.vconst .v128 c),
          .plain (.vstoreLane .v128 sz x ao j)]⟩
        (.vstoreLaneVal x (sz.toNat / 8)) ⟨z', []⟩
  | memoryGrowSucceed {z z' : State} {att : AddrType} {n sz : AddrLit att}
      {x : MemIdx} {mi mi' : MemInst} :
      z.memOf x = some mi → growMem mi n.val = some mi' →
      z.withMemInst x mi' = some z' → sz.val = mi.bytes.length / (64 * Ki) →
      StepA ⟨z, [constAddr att n, .plain (.memoryGrow x)]⟩
        (.memoryGrowSucceed x n.val (mi.bytes.length / (64 * Ki))
          (mi'.bytes.length / (64 * Ki)))
        ⟨z', [constAddr att sz]⟩
  | memoryGrowFail {z : State} {att : AddrType} {n : AddrLit att} {x : MemIdx}
      {e : AddrLit att} :
      e = Numerics.inv_signed_ (addrSize att) (-1) →
      StepA ⟨z, [constAddr att n, .plain (.memoryGrow x)]⟩
        (.memoryGrowFail x n.val) ⟨z, [constAddr att e]⟩
  | dataDrop {z z' : State} {x : DataIdx} :
      z.withData x [] = some z' →
      StepA ⟨z, [.plain (.dataDrop x)]⟩ (.dataDrop x) ⟨z', []⟩
  | structNew {z : State} {vs : List Val} {x : TypeIdx} {dt : DefType}
      {fts : FieldTypes} {n : Nat} {a : StructAddr} {fvs : List FieldVal}
      {si : StructInst} :
      z.typeOf x = some dt → Expand dt (.struct fts) →
      fts.toList.length = n → vs.length = n → a = z.structinst.length →
      (fts.toList.zip vs).mapM
        (fun p => releasedNumerics.packfield_ (fieldStorage p.1) p.2) = some fvs →
      si = { type := dt, fields := fvs } →
      StepA ⟨z, vals vs ++ [.plain (.structNew x)]⟩ (.structNew x n)
        ⟨z.addStructInst [si], [.addrref (.structAddr a)]⟩
  | structSetNull {z : State} {ht : HeapType} {v : Val} {x : TypeIdx}
      {i : U32} :
      StepA ⟨z, [Ref.toAdmin (.null ht), v.toAdmin, .plain (.structSet x i)]⟩
        (.structSetNull x i) ⟨z, [.trap]⟩
  | structSetStruct {z z' : State} {a : StructAddr} {v : Val} {x : TypeIdx}
      {i : U32} {dt : DefType} {fts : FieldTypes} {ft : FieldType}
      {fv : FieldVal} :
      z.typeOf x = some dt → Expand dt (.struct fts) →
      fts.toList[i.val]? = some ft →
      releasedNumerics.packfield_ (fieldStorage ft) v = some fv →
      z.withStruct a i.val fv = some z' →
      StepA ⟨z, [.addrref (.structAddr a), v.toAdmin,
          .plain (.structSet x i)]⟩
        (.structSetStruct x i) ⟨z', []⟩
  | arrayNewFixed {z : State} {vs : List Val} {x : TypeIdx} {n : U32}
      {dt : DefType} {ft : FieldType} {a : ArrayAddr} {fvs : List FieldVal}
      {ai : ArrayInst} :
      z.typeOf x = some dt → Expand dt (.array ft) → vs.length = n.val →
      a = z.arrayinst.length →
      vs.mapM (fun v => releasedNumerics.packfield_ (fieldStorage ft) v) =
        some fvs →
      ai = { type := dt, fields := fvs } →
      StepA ⟨z, vals vs ++ [.plain (.arrayNewFixed x n)]⟩
        (.arrayNewFixed x n.val)
        ⟨z.addArrayInst [ai], [.addrref (.arrayAddr a)]⟩
  | arraySetNull {z : State} {ht : HeapType} {i : U32} {v : Val}
      {x : TypeIdx} :
      StepA ⟨z, [Ref.toAdmin (.null ht), constI32 i, v.toAdmin,
          .plain (.arraySet x)]⟩ (.arraySetNull x) ⟨z, [.trap]⟩
  | arraySetOob {z : State} {a : ArrayAddr} {i : U32} {v : Val}
      {x : TypeIdx} {ai : ArrayInst} :
      z.arrayinst[a]? = some ai → i.val ≥ ai.fields.length →
      StepA ⟨z, [.addrref (.arrayAddr a), constI32 i, v.toAdmin,
          .plain (.arraySet x)]⟩ (.arraySetOob x) ⟨z, [.trap]⟩
  | arraySetArray {z z' : State} {a : ArrayAddr} {i : U32} {v : Val}
      {x : TypeIdx} {dt : DefType} {ft : FieldType} {fv : FieldVal} :
      z.typeOf x = some dt → Expand dt (.array ft) →
      releasedNumerics.packfield_ (fieldStorage ft) v = some fv →
      z.withArray a i.val fv = some z' →
      StepA ⟨z, [.addrref (.arrayAddr a), constI32 i, v.toAdmin,
          .plain (.arraySet x)]⟩ (.arraySetArray x) ⟨z', []⟩

/-! ## Erasure and completeness -/

theorem StepA.erase {c c' : Config} {ev : Event} (h : StepA c ev c') :
    StepEraseA c.1 c.2 c'.1 c'.2 := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction h
  case pure hp => exact .pure (mem_pureSuccessors_step_pure hp)
  case read hr => exact .read hr
  case ctxtInstrs _ hnon ih => exact .ctxtInstrs ih hnon
  case ctxtLabel _ ih => exact .ctxtLabel ih
  case ctxtFrame _ ih => exact .ctxtFrame ih
  case throw => apply Step.throw <;> assumption
  case localSet => apply Step.localSet <;> assumption
  case globalSet => apply Step.globalSet <;> assumption
  case tableSetOob => apply Step.tableSetOob <;> assumption
  case tableSetVal => apply Step.tableSetVal <;> assumption
  case tableGrowSucceed => apply Step.tableGrowSucceed <;> assumption
  case tableGrowFail => apply Step.tableGrowFail <;> assumption
  case elemDrop => apply Step.elemDrop <;> assumption
  case storeNumOob => apply Step.storeNumOob <;> assumption
  case storeNumVal => apply Step.storeNumVal <;> assumption
  case storePackOob => apply Step.storePackOob <;> assumption
  case storePackVal => apply Step.storePackVal <;> assumption
  case vstoreOob => apply Step.vstoreOob <;> assumption
  case vstoreVal => apply Step.vstoreVal <;> assumption
  case vstoreLaneOob => apply Step.vstoreLaneOob <;> assumption
  case vstoreLaneVal => apply Step.vstoreLaneVal <;> assumption
  case memoryGrowSucceed => apply Step.memoryGrowSucceed <;> assumption
  case memoryGrowFail => apply Step.memoryGrowFail <;> assumption
  case dataDrop => apply Step.dataDrop <;> assumption
  case structNew => apply Step.structNew <;> assumption
  case structSetNull => exact .structSetNull
  case structSetStruct => apply Step.structSetStruct <;> assumption
  case arrayNewFixed => apply Step.arrayNewFixed <;> assumption
  case arraySetNull => exact .arraySetNull
  case arraySetOob => apply Step.arraySetOob <;> assumption
  case arraySetArray => apply Step.arraySetArray <;> assumption

theorem stepA_complete {z z' : State} {is is' : List AdminInstr}
    (h : StepEraseA z is z' is') : ∃ ev, StepA (z, is) ev (z', is') := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction h with
  | pure hp =>
      obtain ⟨pe, hpe⟩ := step_pure_mem_pureSuccessors hp
      exact ⟨.pure pe (sourcePlains _), .pure hpe⟩
  | @read z rule is is' hr =>
      exact ⟨.read rule (sourcePlains is), .read hr⟩
  | @ctxtInstrs z z' vs is is' is₁ hstep hnon ih =>
      obtain ⟨ev, hev⟩ := ih
      exact ⟨.ctxtInstrs vs.length is₁.length ev, .ctxtInstrs hev hnon⟩
  | @ctxtLabel z z' n cont is is' hstep ih =>
      obtain ⟨ev, hev⟩ := ih
      exact ⟨.ctxtLabel n ev, .ctxtLabel hev⟩
  | @ctxtFrame s s' f f' f'' n is is' hstep ih =>
      obtain ⟨ev, hev⟩ := ih
      exact ⟨.ctxtFrame n ev, .ctxtFrame hev⟩
  | @throw z vs x ti dt t n a ta ex htag hdt hexpand ht hvs ha hta hex =>
      exact ⟨.throw x n, .throw htag hdt hexpand ht hvs ha hta hex⟩
  | @localSet z z' v x hset => exact ⟨.localSet x, .localSet hset⟩
  | @globalSet z z' v x hset => exact ⟨.globalSet x, .globalSet hset⟩
  | @tableSetOob z att i r x ti htable hoob =>
      exact ⟨.tableSetOob x, .tableSetOob htable hoob⟩
  | @tableSetVal z z' att i r x ti htable hin hset =>
      exact ⟨.tableSetVal x, .tableSetVal htable hin hset⟩
  | @tableGrowSucceed z z' att n sz r x ti ti' htable hgrow hset hsz =>
      exact ⟨.tableGrowSucceed x n.val ti.refs.length ti'.refs.length,
        .tableGrowSucceed htable hgrow hset hsz⟩
  | @tableGrowFail z att n r x e he =>
      exact ⟨.tableGrowFail x n.val, .tableGrowFail he⟩
  | @elemDrop z z' x hdrop => exact ⟨.elemDrop x, .elemDrop hdrop⟩
  | @storeNumOob z att i nt c x ao mi hmem hoob =>
      exact ⟨.storeNumOob x (nt.size / 8), .storeNumOob hmem hoob⟩
  | @storeNumVal z z' att i nt c x ao bs hbs hmem =>
      exact ⟨.storeNumVal x (nt.size / 8), .storeNumVal hbs hmem⟩
  | @storePackOob z att i inn c sz x ao mi hmem hoob =>
      exact ⟨.storePackOob x (sz.toNat / 8), .storePackOob hmem hoob⟩
  | @storePackVal z z' att i inn c sz x ao bs hbs hmem =>
      exact ⟨.storePackVal x (sz.toNat / 8), .storePackVal hbs hmem⟩
  | @vstoreOob z att i c x ao mi hmem hoob =>
      exact ⟨.vstoreOob x (VecType.v128.size / 8), .vstoreOob hmem hoob⟩
  | @vstoreVal z z' att i c x ao bs hbs hmem =>
      exact ⟨.vstoreVal x (VecType.v128.size / 8), .vstoreVal hbs hmem⟩
  | @vstoreLaneOob z att i c sz x ao j mi hmem hoob =>
      exact ⟨.vstoreLaneOob x (sz.toNat / 8), .vstoreLaneOob hmem hoob⟩
  | @vstoreLaneVal z z' att i c sz x ao j sh lv k bs hsz hdim hlane hk hbs hmem =>
      exact ⟨.vstoreLaneVal x (sz.toNat / 8),
        .vstoreLaneVal hsz hdim hlane hk hbs hmem⟩
  | @memoryGrowSucceed z z' att n sz x mi mi' hmem hgrow hset hsz =>
      exact ⟨.memoryGrowSucceed x n.val (mi.bytes.length / (64 * Ki))
          (mi'.bytes.length / (64 * Ki)),
        .memoryGrowSucceed hmem hgrow hset hsz⟩
  | @memoryGrowFail z att n x e he =>
      exact ⟨.memoryGrowFail x n.val, .memoryGrowFail he⟩
  | @dataDrop z z' x hdrop => exact ⟨.dataDrop x, .dataDrop hdrop⟩
  | @structNew z vs x dt fts n a fvs si htype hexpand hfts hvs ha hpack hsi =>
      exact ⟨.structNew x n,
        .structNew htype hexpand hfts hvs ha hpack hsi⟩
  | @structSetNull z ht v x i => exact ⟨.structSetNull x i, .structSetNull⟩
  | @structSetStruct z z' a v x i dt fts ft fv htype hexpand hfield hpack hset =>
      exact ⟨.structSetStruct x i,
        .structSetStruct htype hexpand hfield hpack hset⟩
  | @arrayNewFixed z vs x n dt ft a fvs ai htype hexpand hlen ha hpack hai =>
      exact ⟨.arrayNewFixed x n.val,
        .arrayNewFixed htype hexpand hlen ha hpack hai⟩
  | @arraySetNull z ht i v x => exact ⟨.arraySetNull x, .arraySetNull⟩
  | @arraySetOob z a i v x ai harray hoob =>
      exact ⟨.arraySetOob x, .arraySetOob harray hoob⟩
  | @arraySetArray z z' a i v x dt ft fv htype hexpand hpack hset =>
      exact ⟨.arraySetArray x, .arraySetArray htype hexpand hpack hset⟩

theorem stepA_iff_erased (z z' : State) (is is' : List AdminInstr) :
    (∃ ev, StepA (z, is) ev (z', is')) ↔ StepEraseA z is z' is' :=
  ⟨fun h => h.elim (fun _ hs => hs.erase), stepA_complete⟩

/-- Event traces of zero or more released Core steps. -/
inductive StepsA : Config → List Event → Config → Prop where
  | refl (c : Config) : StepsA c [] c
  | cons {c c' c'' : Config} {ev : Event} {trace : List Event} :
      StepA c ev c' → StepsA c' trace c'' → StepsA c (ev :: trace) c''

theorem StepsA.erase {c c' : Config} {trace : List Event}
    (h : StepsA c trace c') : StepsEraseA c.1 c.2 c'.1 c'.2 := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  induction h
  case refl c =>
      exact @Steps.refl amendedExecutionAuthority releasedNumerics c.1 c.2
  case cons hs _ ih =>
      exact @Steps.trans amendedExecutionAuthority releasedNumerics
        _ _ _ _ _ _ hs.erase ih

theorem stepsA_complete {z z' : State} {is is' : List AdminInstr}
    (h : StepsEraseA z is z' is') : ∃ trace, StepsA (z, is) trace (z', is') := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | trans hs _ ih =>
      obtain ⟨ev, hev⟩ := stepA_complete hs
      obtain ⟨trace, htrace⟩ := ih
      exact ⟨ev :: trace, .cons hev htrace⟩

/-- Event-labelled evaluation of an expression to a value sequence. -/
inductive Eval_exprA : State → Expr → List Event → State → List Val → Prop where
  | mk {z z' : State} {e : Expr} {trace : List Event} {vs : List Val} :
      StepsA (z, exprAdmin e) trace (z', vals vs) →
      Eval_exprA z e trace z' vs

theorem Eval_exprA.erase {z z' : State} {e : Expr} {trace : List Event}
    {vs : List Val} (h : Eval_exprA z e trace z' vs) :
    Eval_exprEraseA z e z' vs := by
  letI : ExecutionAuthority := amendedExecutionAuthority
  cases h with
  | mk hs => exact .mk hs.erase

theorem eval_exprA_complete {z z' : State} {e : Expr} {vs : List Val}
    (h : Eval_exprEraseA z e z' vs) :
    ∃ trace, Eval_exprA z e trace z' vs := by
  cases h with
  | mk hs =>
      obtain ⟨trace, htrace⟩ := stepsA_complete hs
      exact ⟨trace, .mk htrace⟩

end WasmGemmGnaf.Wasm.Core.Exec
