/-
  Wasm/Core/CostAccounting.lean --- static cost inputs for the public amended
  Core carrier.

  This file is deliberately below `Cost/Aggregate.lean`.  Aggregate cost uses
  these functions, so importing the aggregate layer here would make the public
  cost definition circular.
-/
import WasmGemmGnaf.Wasm.CoreFrontEnd
import WasmGemmGnaf.Wasm.Profile

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

/-- **SPEC section 7.5, `Wasm.decodeCost`.**  One unit per consumed byte and
one terminal accept/reject unit, at the exact rates carried by the first-order
cost table. -/
def decodeCost (table : CostTableBody) (bytes : ByteArray) : Nat :=
  table.decodeCost bytes

/-! ## Canonical validation-tree size

The validation charge is computed from a deterministic tree over the complete
module syntax.  Every sequence constructor and every instruction contributes
one node; structured instructions recursively include each body.  Module
declarations contribute one node apiece and connect each expression they own.
The functions are total because validation itself has a rejecting derivation
attempt for ill-typed syntax too.
-/

mutual

/-- Nodes visited by the canonical validation traversal of one Core
instruction. -/
def Core.Instr.validationNodes : Core.Instr → Nat
  | .block _ body => 1 + Core.InstrSeq.validationNodes body
  | .loop _ body => 1 + Core.InstrSeq.validationNodes body
  | .ifElse _ thn els =>
      1 + Core.InstrSeq.validationNodes thn + Core.InstrSeq.validationNodes els
  | .tryTable _ _ body => 1 + Core.InstrSeq.validationNodes body
  | _ => 1

/-- Nodes visited by the canonical validation traversal of a Core instruction
sequence.  The empty-sequence rule is a node; a nonempty sequence has a
composition node and the two recursively checked premises. -/
def Core.InstrSeq.validationNodes : Core.InstrSeq → Nat
  | .nil => 1
  | .cons instruction rest =>
      1 + instruction.validationNodes + rest.validationNodes

end

mutual

/-- Premise edges visited by the canonical validation traversal of one Core
instruction. -/
def Core.Instr.validationEdges : Core.Instr → Nat
  | .block _ body => 1 + Core.InstrSeq.validationEdges body
  | .loop _ body => 1 + Core.InstrSeq.validationEdges body
  | .ifElse _ thn els =>
      2 + Core.InstrSeq.validationEdges thn + Core.InstrSeq.validationEdges els
  | .tryTable _ _ body => 1 + Core.InstrSeq.validationEdges body
  | _ => 0

/-- Premise edges visited by the canonical validation traversal of a Core
instruction sequence. -/
def Core.InstrSeq.validationEdges : Core.InstrSeq → Nat
  | .nil => 0
  | .cons instruction rest =>
      2 + instruction.validationEdges + rest.validationEdges

end


namespace Core

private def modeExprNodes : DataMode → Nat
  | .active _ offset => offset.validationNodes
  | .passive => 0

private def modeExprEdges : DataMode → Nat
  | .active _ offset => 1 + offset.validationEdges
  | .passive => 0

private def elemModeExprNodes : ElemMode → Nat
  | .active _ offset => offset.validationNodes
  | .passive => 0
  | .declare => 0

private def elemModeExprEdges : ElemMode → Nat
  | .active _ offset => 1 + offset.validationEdges
  | .passive => 0
  | .declare => 0

/-- Nodes of the deterministic whole-module validation traversal.  Section
lists are traversed in the source order fixed by `Core.Module`; expression
owners connect to the recursive expression traversal above. -/
def Module.validationNodes (module : Core.Module) : Nat :=
  1 +
    module.types.length + module.imports.length + module.tags.length +
    (module.globals.map (fun global => 1 + global.init.validationNodes)).sum +
    module.mems.length +
    (module.tables.map (fun table => 1 + table.init.validationNodes)).sum +
    (module.funcs.map (fun func => 1 + func.body.validationNodes)).sum +
    (module.datas.map (fun data => 1 + modeExprNodes data.mode)).sum +
    (module.elems.map (fun elem =>
      1 + (elem.init.map InstrSeq.validationNodes).sum +
        elemModeExprNodes elem.mode)).sum +
    (if module.start.isSome then 1 else 0) + module.exports.length

/-- Premise edges of the deterministic whole-module validation traversal. -/
def Module.validationEdges (module : Core.Module) : Nat :=
  module.types.length + module.imports.length + module.tags.length +
    (module.globals.map (fun global => 1 + global.init.validationEdges)).sum +
    module.mems.length +
    (module.tables.map (fun table => 1 + table.init.validationEdges)).sum +
    (module.funcs.map (fun func => 1 + func.body.validationEdges)).sum +
    (module.datas.map (fun data => 1 + modeExprEdges data.mode)).sum +
    (module.elems.map (fun elem =>
      1 + (elem.init.map (fun init => 1 + init.validationEdges)).sum +
        elemModeExprEdges elem.mode)).sum +
    (if module.start.isSome then 1 else 0) + module.exports.length

end Core

/-- **SPEC section 7.5, `Wasm.validationCost`.**  Charge the public amended
Core module's deterministic validation tree at the profile's node and premise
edge rates. -/
def validationCost (table : CostTableBody) (module : Module) : Nat :=
  table.validationCost module.core.validationNodes module.core.validationEdges

/-! ## Static bytes materialised by instantiation -/

/-- Abstract byte width of an amended-Core value type under the profile's
first-order layout constants.  `bot` has no runtime representation and cannot
occur in the syntax of a public representable module. -/
def GcLayoutConstants.coreValTypeWidth
    (layout : GcLayoutConstants) : Core.ValType → Nat
  | .num .i32 => layout.i32Width
  | .num .i64 => layout.i64Width
  | .num .f32 => layout.f32Width
  | .num .f64 => layout.f64Width
  | .vec .v128 => layout.v128Width
  | .ref _ => layout.referenceWidth
  | .bot => 0

/-- Static bytes contributed by one public-Core data segment. -/
def Core.Data.staticBytes (data : Core.Data) : Nat := data.bytes.length

/-- Static bytes contributed by one public-Core element segment. -/
def Core.Elem.staticBytes (layout : GcLayoutConstants) (elem : Core.Elem) : Nat :=
  elem.init.length * layout.referenceWidth

/-- Static bytes contributed by one public-Core global. -/
def Core.Global.staticBytes
    (layout : GcLayoutConstants) (global : Core.Global) : Nat :=
  layout.coreValTypeWidth global.globaltype.valtype

/-- Static bytes contributed by one public-Core linear memory. -/
def Core.Mem.staticBytes (mem : Core.Mem) : Nat :=
  mem.memtype.lim.min.val * pageSize

/-- Static bytes contributed by one public-Core table. -/
def Core.Table.staticBytes
    (layout : GcLayoutConstants) (table : Core.Table) : Nat :=
  table.tabletype.lim.min.val * layout.referenceWidth

/-- **SPEC section 7.5, `Wasm.instantiatedStaticBytes`.**  Exact static bytes
materialised by public amended-Core instantiation: data payloads, element
references, globals, declared initial memory pages, and declared initial table
elements. -/
def instantiatedStaticBytes (profile : Profile) (module : Module) : Nat :=
  let core := module.core
  let layout := profile.costTableBody.layout
  (core.datas.map Core.Data.staticBytes).sum +
    (core.elems.map (Core.Elem.staticBytes layout)).sum +
    (core.globals.map (Core.Global.staticBytes layout)).sum +
    (core.mems.map Core.Mem.staticBytes).sum +
    (core.tables.map (Core.Table.staticBytes layout)).sum

end WasmGemmGnaf.Wasm
