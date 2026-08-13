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

end WasmGemmGnaf.Wasm.Core
