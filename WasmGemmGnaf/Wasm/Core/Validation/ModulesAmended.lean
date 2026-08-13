/-
  Wasm/Core/Validation/ModulesAmended.lean --- the amendment of DEV-006 carried
  up to the FUNCTION level, where the vacuity of the pinned rules actually
  bites.

  `Core/Validate.lean` proves `gapModule_not_ok`: a module whose single function
  body is `(i32.const 0) (i32.const 0) (i32.add)` --- which `validate` accepts
  and every engine accepts --- has NO module type under the pinned rules, because
  `Func_ok` types the body with `Expr_ok`, which types it with `Instrs_ok`, which
  cannot compose it.  That is the whole vacuity argument, and it passes through
  `Func_ok` untouched.

  `Func_ok'` is `Func_ok` with its ONE `Expr_ok` premise replaced by `Expr_ok'`.
  Nothing else changes: the type lookup, `Expand`, and the `Local_ok` iteration
  are the pinned premises verbatim.  `Func_ok.to_amended` proves the amendment
  rejects no function the pinned rule accepts, and `Func_ok'.gapFunc` derives
  the function the pinned rule provably cannot type.

  As in `InstructionsAmended.lean`, no declaration here carries a coverage
  marker: none of this is a transcription of a pinned rule.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Modules
import WasmGemmGnaf.Wasm.Core.Validation.InstructionsAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- `relation Func_ok`, with the body typed by the amended expression
judgment.  Every other premise is the pinned one, verbatim. -/
inductive Func_ok' : Context → Func → DefType → Prop where
  | mk {C : Context} {f : Func} {dt : DefType} {dom cod : ValTypes}
      {lcts : List LocalType} :
      C.types[f.typeidx.val]? = some dt →
      Expand dt (.func dom cod) →
      SeqLen₂ f.locals lcts →
      SeqAll₂ (Local_ok C) f.locals lcts →
      Expr_ok' (Context.append C
          { locals := (ValTypes.toList dom).map (fun t => ⟨.set, t⟩) ++ lcts,
            labels := [ValTypes.toList cod],
            ret := some (ValTypes.toList cod) })
        f.body (ValTypes.toList cod) →
      Func_ok' C f dt

/-- The amendment rejects no function the pinned rule accepts. -/
theorem Func_ok.to_amended {C : Context} {f : Func} {dt : DefType}
    (h : Func_ok C f dt) : Func_ok' C f dt := by
  cases h with
  | mk htys hexp hlen hall hbody =>
      exact .mk htys hexp hlen hall hbody.to_amended

/-! ## The function the pinned rules cannot type

`(func (result i32) i32.const 0  i32.const 0  i32.add)` --- the body of
`Validate.gapModule`, whose rejection by the pinned rules is `gapModule_not_ok`.
Under the amendment it is `Func_ok'`. -/

/-- `(type (func (result i32)))`, as the `deftype` a module's type section
elaborates to. -/
def gapDefType : DefType :=
  .defd (.recr (.cons (.sub (some .final) .nil
    (.func .nil (ValTypes.ofList [ValType.i32]))) .nil)) 0

/-- A context whose single type is `gapDefType`. -/
def gapContext : Context := { Context.empty with types := [gapDefType] }

/-- `(func (result i32) i32.const 0  i32.const 0  i32.add)`. -/
def gapFunc : Func :=
  { typeidx := TypeIdx.ofNat 0, locals := [],
    body := InstrSeq.ofList
      [Instr.const .i32 default, Instr.const .i32 default,
       Instr.binop .i32 (.int .add)] }

/-- **THE VACUITY, CLOSED AT THE LEVEL IT WAS STATED.**  The pinned rules give
`gapFunc` no `Func_ok` --- that is what makes `Validate.gapModule_not_ok` true
and `Module_ok` near-vacuous.  The amended rule types it, at exactly the
`deftype` the module's type section declares. -/
theorem Func_ok'.gapFunc : Func_ok' gapContext gapFunc gapDefType := by
  refine .mk (dom := .nil) (cod := ValTypes.ofList [ValType.i32]) (lcts := [])
    rfl (.mk rfl) rfl (fun _ _ _ h _ => nomatch h) ?_
  refine .mk ?_
  simp only [gapFunc, InstrSeq.toList_ofList, ValTypes.toList_ofList]
  exact Instrs_ok'.const_const_binop rfl

/-! ## The amendment carried to the MODULE level

Every module-level rule that reaches the instruction judgment does so through
`Expr_ok` or `Expr_ok_const`, so each of them gets one primed copy with that
single premise replaced and NOTHING else changed.  `Type_ok`, `Types_ok`,
`Tag_ok`, `Mem_ok`, `Local_ok`, `Start_ok`, `Externidx_ok`, `Import_ok` and
`Export_ok` mention no expression and are reused verbatim.

`Module_ok'` is then `Module_ok` with the six primed premises substituted; the
twenty-two remaining premises, the two staged contexts, `$funcidx_nonfuncs`,
`$disjoint_` and `$clos_moduletype` are the pinned ones, character for
character.  `Module_ok.to_amended` proves the amendment rejects no module the
pinned rule accepts. -/

/-- `relation Expr_ok_const`, over the amended expression judgment.  `Expr_const`
is syntactic and unchanged. -/
inductive Expr_ok_const' : Context → Expr → ValType → Prop where
  | mk {C : Context} {e : Expr} {t : ValType} :
      Expr_ok' C e [t] → Expr_const C e → Expr_ok_const' C e t

theorem Expr_ok_const.to_amended {C : Context} {e : Expr} {t : ValType}
    (h : Expr_ok_const C e t) : Expr_ok_const' C e t := by
  cases h with
  | mk hok hc => exact .mk hok.to_amended hc

/-- `relation Global_ok`, over the amended constant-expression judgment. -/
inductive Global_ok' : Context → Global → GlobalType → Prop where
  | mk {C : Context} {g : Global} :
      Globaltype_ok C g.globaltype →
      Expr_ok_const' C g.init g.globaltype.valtype →
      Global_ok' C g g.globaltype

theorem Global_ok.to_amended {C : Context} {g : Global} {gt : GlobalType}
    (h : Global_ok C g gt) : Global_ok' C g gt := by
  cases h with
  | mk hty hc => exact .mk hty hc.to_amended

/-- `relation Table_ok`, over the amended constant-expression judgment. -/
inductive Table_ok' : Context → Table → TableType → Prop where
  | mk {C : Context} {t : Table} :
      Tabletype_ok C t.tabletype →
      Expr_ok_const' C t.init (.ref t.tabletype.elem) →
      Table_ok' C t t.tabletype

theorem Table_ok.to_amended {C : Context} {t : Table} {tt : TableType}
    (h : Table_ok C t tt) : Table_ok' C t tt := by
  cases h with
  | mk hty hc => exact .mk hty hc.to_amended

/-- `relation Datamode_ok`, over the amended constant-expression judgment. -/
inductive Datamode_ok' : Context → DataMode → DataType → Prop where
  | passive {C : Context} : Datamode_ok' C .passive .ok
  | active {C : Context} {x : MemIdx} {e : Expr} {mt : MemType} :
      C.mems[x.val]? = some mt →
      Expr_ok_const' C e mt.addr.toValType →
      Datamode_ok' C (.active x e) .ok

/-- `relation Data_ok`, over the amended data-mode judgment. -/
inductive Data_ok' : Context → Data → DataType → Prop where
  | mk {C : Context} {d : Data} : Datamode_ok' C d.mode .ok → Data_ok' C d .ok

theorem Datamode_ok.to_amended {C : Context} {dm : DataMode} {dt : DataType}
    (h : Datamode_ok C dm dt) : Datamode_ok' C dm dt := by
  cases h with
  | passive => exact .passive
  | active hmem hc => exact .active hmem hc.to_amended

theorem Data_ok.to_amended {C : Context} {d : Data} {dt : DataType}
    (h : Data_ok C d dt) : Data_ok' C d dt := by
  cases h with
  | mk hm => exact .mk hm.to_amended

/-- `relation Elemmode_ok`, over the amended constant-expression judgment. -/
inductive Elemmode_ok' : Context → ElemMode → ElemType → Prop where
  | passive {C : Context} {rt : ElemType} : Elemmode_ok' C .passive rt
  | declare {C : Context} {rt : ElemType} : Elemmode_ok' C .declare rt
  | active {C : Context} {x : TableIdx} {e : Expr} {tt : TableType} {rt : ElemType} :
      C.tables[x.val]? = some tt →
      Reftype_sub C rt tt.elem →
      Expr_ok_const' C e tt.addr.toValType →
      Elemmode_ok' C (.active x e) rt

/-- `relation Elem_ok`, over the amended constant-expression judgment. -/
inductive Elem_ok' : Context → Elem → ElemType → Prop where
  | mk {C : Context} {e : Elem} :
      Reftype_ok C e.reftype →
      SeqAll (fun (ex : Expr) => Expr_ok_const' C ex (.ref e.reftype)) e.init →
      Elemmode_ok' C e.mode e.reftype →
      Elem_ok' C e e.reftype

theorem Elemmode_ok.to_amended {C : Context} {em : ElemMode} {rt : ElemType}
    (h : Elemmode_ok C em rt) : Elemmode_ok' C em rt := by
  cases h with
  | passive => exact .passive
  | declare => exact .declare
  | active htab hsub hc => exact .active htab hsub hc.to_amended

theorem Elem_ok.to_amended {C : Context} {e : Elem} {rt : ElemType}
    (h : Elem_ok C e rt) : Elem_ok' C e rt := by
  cases h with
  | mk hrt hinit hmode =>
      exact .mk hrt (fun ex hex => (hinit ex hex).to_amended) hmode.to_amended

/-- `relation Globals_ok`, over the amended global judgment. -/
inductive Globals_ok' : Context → List Global → List GlobalType → Prop where
  | empty {C : Context} : Globals_ok' C [] []
  | cons {C : Context} {g : Global} {gs : List Global}
      {gt₁ : GlobalType} {gts : List GlobalType} :
      Global_ok' C g gt₁ →
      Globals_ok' (Context.append C { globals := [gt₁] }) gs gts →
      Globals_ok' C (g :: gs) (gt₁ :: gts)

theorem Globals_ok.to_amended {C : Context} {gs : List Global} {gts : List GlobalType}
    (h : Globals_ok C gs gts) : Globals_ok' C gs gts := by
  induction h with
  | empty => exact .empty
  | cons hg _ ih => exact .cons hg.to_amended ih

/-- `relation Module_ok`, over the amended function, global, table, data and
element judgments.  Every other premise is the pinned one. -/
inductive Module_ok' : Module → ModuleType → Prop where
  | mk {m : Module} {C C' : Context}
      {dts' : List DefType} {xtsI xtsE : List ExternType}
      {jts : List TagType} {gts : List GlobalType} {mts : List MemType}
      {tts : List TableType} {dts : List DefType} {oks : List DataType}
      {rts : List ElemType} {nms : List Name}
      {jtsI : List TagType} {gtsI : List GlobalType} {mtsI : List MemType}
      {ttsI : List TableType} {dtsI : List DefType} {xs : List FuncIdx} :
      Types_ok Context.empty m.types dts' →
      SeqLen₂ m.imports xtsI →
      SeqAll₂ (Import_ok { Context.empty with types := dts' }) m.imports xtsI →
      SeqLen₂ m.tags jts →
      SeqAll₂ (Tag_ok C') m.tags jts →
      Globals_ok' C' m.globals gts →
      SeqLen₂ m.mems mts →
      SeqAll₂ (Mem_ok C') m.mems mts →
      SeqLen₂ m.tables tts →
      SeqAll₂ (Table_ok' C') m.tables tts →
      SeqLen₂ m.funcs dts →
      SeqAll₂ (Func_ok' C) m.funcs dts →
      SeqLen₂ m.datas oks →
      SeqAll₂ (Data_ok' C) m.datas oks →
      SeqLen₂ m.elems rts →
      SeqAll₂ (Elem_ok' C) m.elems rts →
      OptAll (Start_ok C) m.start →
      SeqLen₃ m.exports nms xtsE →
      SeqAll₃ (Export_ok C) m.exports nms xtsE →
      disjoint nms = true →
      C = Context.append C'
        { tags := jtsI ++ jts, globals := gts, mems := mtsI ++ mts,
          tables := ttsI ++ tts, datas := oks, elems := rts } →
      C' = { types := dts', globals := gtsI, funcs := dtsI ++ dts, refs := xs } →
      xs = funcidxNonfuncs m.globals m.mems m.tables m.elems →
      jtsI = ExternType.tags xtsI →
      gtsI = ExternType.globals xtsI →
      mtsI = ExternType.mems xtsI →
      ttsI = ExternType.tables xtsI →
      funcsXt xtsI = some dtsI →
      Module_ok' m (C.closModuleType ⟨xtsI, xtsE⟩)

/-- **THE AMENDMENT REJECTS NO MODULE THE PINNED RULE ACCEPTS.**  This is the
module-level form of `Instrs_ok.to_amended`: the amendment is a widening, and
the containment is proved rather than asserted. -/
theorem Module_ok.to_amended {m : Module} {mt : ModuleType} (h : Module_ok m mt) :
    Module_ok' m mt := by
  cases h with
  | mk hty hli hi hlj hj hg hlm hm hlt ht hlf hf hld hd hle he hs hlx hx hdis
      hC hC' hxs hjI hgI hmI htI hdI =>
      exact .mk hty hli hi hlj hj hg.to_amended hlm hm hlt
        (fun i a b ha hb => (ht i a b ha hb).to_amended) hlf
        (fun i a b ha hb => (hf i a b ha hb).to_amended) hld
        (fun i a b ha hb => (hd i a b ha hb).to_amended) hle
        (fun i a b ha hb => (he i a b ha hb).to_amended) hs hlx hx hdis
        hC hC' hxs hjI hgI hmI htI hdI

end WasmGemmGnaf.Wasm.Core
