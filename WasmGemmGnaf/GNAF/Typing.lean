import WasmGemmGnaf.GNAF.Resource
import WasmGemmGnaf.Gemm.Problem
set_option autoImplicit false

/-!
# GNAF: typing (SPEC §11.2)

SPEC §11.2: "Every plan SHALL carry exact input/output types and resource
transitions."  A `Sig` is that interface — the exact input and output type
instances together with the register, vector-register, lane, scratch, table and
memory resources, and the status flag.  `HasType s p t` is the typing judgment:
running `p` at interface `s` leaves interface `t`.

The judgment is *decidable*: `infer` is a total decision procedure, proved

* sound (`infer_sound`: whatever it accepts really is derivable), and
* complete (`infer_complete`: whatever is derivable it accepts),

so `hasType_iff_infer` makes the relation and the procedure interchangeable and
`instDecidableHasType` follows.  Nothing is assumed about the procedure.

The opaque-process rule is where SPEC §11.1's "opaque SHALL not mean trusted"
becomes formal: `HasType` admits `opaqueProcess spec body` only when the
declared step and byte certificate equal the values *recomputed* from the
retained body.

The final section proves the judgment sound for the semantics of
`GNAF/Semantics.lean`: `Machine.Conforms` links a configuration to an
interface, and `hasType_preservation` shows a well-typed plan maps conforming
configurations to conforming configurations.
-/

namespace WasmGemmGnaf.GNAF

open WasmGemmGnaf.Foundation

/-! ## Interfaces -/

/-- The exact interface of a plan (SPEC §11.2): input and output type
instances, plus the complete resource state. -/
structure Sig where
  /-- The type instance of the raw input. -/
  inputType : ObjType
  /-- The type instance of the constructed output. -/
  outputType : ObjType
  /-- Size of the scalar register file. -/
  regs : Nat
  /-- Size of the vector register file. -/
  vregs : Nat
  /-- Maximum admitted vector lane count. -/
  lanes : Nat
  /-- Declared scratch extent. -/
  scratch : Nat
  /-- Number of code/data tables. -/
  tables : Nat
  /-- Observable memory extent. -/
  mem : Nat
  /-- Whether a status has been constructed. -/
  statusSet : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Cond

/-- A condition is well typed at an interface when every register it reads
exists. -/
def wellTyped (c : Cond) (s : Sig) : Bool :=
  match c with
  | regEq r _ => decide (r < s.regs)
  | regLt r _ => decide (r < s.regs)
  | _ => true

end Cond

/-! ## The typing judgment -/

/-- `HasType s p t`: at input interface `s`, plan `p` is well typed and leaves
output interface `t` (SPEC §11.2). -/
inductive HasType : Sig → Plan → Sig → Prop
  | nop (s : Sig) : HasType s .nop s
  | seq {s u t : Sig} {a b : Plan} :
      HasType s a u → HasType u b t → HasType s (.seq a b) t
  | classifyRaw {s t : Sig} {v i u e : Plan} :
      HasType s v t → HasType s i t → HasType s u t → HasType s e t →
      HasType s (.classifyRaw v i u e) t
  | dispatchLayout {s t : Sig} {r c g : Plan} :
      HasType s r t → HasType s c t → HasType s g t →
      HasType s (.dispatchLayout r c g) t
  | branch {s t : Sig} {co : Cond} {x y : Plan} :
      co.wellTyped s = true → HasType s x t → HasType s y t →
      HasType s (.branch co x y) t
  | pack {s : Sig} {src dst : RegionRef} {map : IndexMap} {w : Nat} :
      src.Fits s.mem → dst.Fits s.scratch → 0 < w →
      HasType s (.pack src dst map w) s
  | unpack {s : Sig} {src dst : RegionRef} {map : IndexMap} {w : Nat} :
      src.Fits s.scratch → dst.Fits s.mem → 0 < w →
      HasType s (.unpack src dst map w) s
  | storeReg {s : Sig} {dst : RegionRef} {map : IndexMap} {w src : Nat} :
      dst.Fits s.mem → 0 < w → src < s.regs → 2 < s.regs →
      HasType s (.storeReg dst map w src) s
  | loadReg {s : Sig} {dst : Nat} {src : RegionRef} {map : IndexMap} {w : Nat} :
      src.Fits s.mem → 0 < w → dst < s.regs → 2 < s.regs →
      HasType s (.loadReg dst src map w) s
  | loopNest {s : Sig} {axis : LoopAxis} {body : Plan} :
      axis.indexReg < s.regs → HasType s body s → HasType s (.loopNest axis body) s
  | loopReg {s : Sig} {ir er : Nat} {map : IndexMap} {body : Plan} :
      ir < s.regs → er < s.regs → HasType s body s →
      HasType s (.loopReg ir er map body) s
  | tiled {s : Sig} {o : TraversalOrder} {ti : Tiling} {ex : Extents} {body : Plan} :
      ti.Positive → HasType s body s → HasType s (.tiled o ti ex body) s
  | reduce {s : Sig} {c : ArithmeticContract} {acc : Nat} {lhs rhs : RegionRef} :
      acc < s.regs → c.compatibleB = true → lhs.Fits s.mem → rhs.Fits s.mem →
      HasType s (.reduce c acc lhs rhs) s
  | allocScratch {s t : Sig} {n : Nat} {body : Plan} :
      HasType { s with scratch := s.scratch + n } body t →
      HasType s (.allocScratch n body) t
  | setReg {s : Sig} {dst v : Nat} : dst < s.regs → HasType s (.setReg dst v) s
  | scalarOp {s : Sig} {op : ScalarOp} {dst a b : Nat} :
      dst < s.regs → a < s.regs → b < s.regs → HasType s (.scalarOp op dst a b) s
  | vectorOp {s : Sig} {op : VectorOp} {lanes dst a b : Nat} :
      0 < lanes → lanes ≤ s.lanes → dst < s.vregs → a < s.vregs → b < s.vregs →
      HasType s (.vectorOp op lanes dst a b) s
  | emitTable {s : Sig} {idx : Nat} {data : List Nat} :
      idx < s.tables → HasType s (.emitTable idx data) s
  | tableLoad {s : Sig} {tbl idx dst : Nat} :
      tbl < s.tables → dst < s.regs → HasType s (.tableLoad tbl idx dst) s
  | setStatus (s : Sig) (st : Status) :
      HasType s (.setStatus st) { s with statusSet := true }
  | buildOutput {s : Sig} {src : RegionRef} :
      s.statusSet = true → src.Fits s.mem →
      HasType s (.buildOutput src) { s with outputType := .bytes src.count }
  | opaqueProcess {s t : Sig} {spec : OpaqueSpec} {body : Plan} :
      spec.declaredSteps = body.stepBound →
      spec.declaredBytes = body.charges.moduleBytes →
      HasType s body t → HasType s (.opaqueProcess spec body) t

/-! ## The decision procedure -/

/-- Join of two inferred interfaces: defined only when both exist and agree. -/
def joinSig : Option Sig → Option Sig → Option Sig
  | some a, some b => if a = b then some a else none
  | _, _ => none

theorem joinSig_eq_some {x y : Option Sig} {t : Sig} :
    joinSig x y = some t ↔ x = some t ∧ y = some t := by
  cases x with
  | none => simp [joinSig]
  | some a =>
    cases y with
    | none => simp [joinSig]
    | some b =>
      by_cases h : a = b
      · subst h; simp [joinSig]
      · simp [joinSig, h]
        intro ht
        subst ht
        exact fun hb => absurd hb.symm h

/-- The typing decision procedure: it computes the unique output interface, or
rejects. -/
def infer : Sig → Plan → Option Sig
  | s, .nop => some s
  | s, .seq a b =>
      match infer s a with
      | some u => infer u b
      | none => none
  | s, .classifyRaw v i u e =>
      joinSig (joinSig (infer s v) (infer s i)) (joinSig (infer s u) (infer s e))
  | s, .dispatchLayout r c g =>
      joinSig (infer s r) (joinSig (infer s c) (infer s g))
  | s, .branch co x y =>
      if co.wellTyped s = true then joinSig (infer s x) (infer s y) else none
  | s, .pack src dst _ w =>
      if src.Fits s.mem ∧ dst.Fits s.scratch ∧ 0 < w then some s else none
  | s, .unpack src dst _ w =>
      if src.Fits s.scratch ∧ dst.Fits s.mem ∧ 0 < w then some s else none
  | s, .storeReg dst _ w src =>
      if dst.Fits s.mem ∧ 0 < w ∧ src < s.regs ∧ 2 < s.regs then some s else none
  | s, .loadReg dst src _ w =>
      if src.Fits s.mem ∧ 0 < w ∧ dst < s.regs ∧ 2 < s.regs then some s else none
  | s, .loopNest axis body =>
      if axis.indexReg < s.regs ∧ infer s body = some s then some s else none
  | s, .loopReg ir er _ body =>
      if ir < s.regs ∧ er < s.regs ∧ infer s body = some s then some s else none
  | s, .tiled _ ti _ body =>
      if ti.Positive ∧ infer s body = some s then some s else none
  | s, .reduce c acc lhs rhs =>
      if acc < s.regs ∧ c.compatibleB = true ∧ lhs.Fits s.mem ∧ rhs.Fits s.mem then
        some s else none
  | s, .allocScratch n body => infer { s with scratch := s.scratch + n } body
  | s, .setReg dst _ => if dst < s.regs then some s else none
  | s, .scalarOp _ dst a b =>
      if dst < s.regs ∧ a < s.regs ∧ b < s.regs then some s else none
  | s, .vectorOp _ lanes dst a b =>
      if 0 < lanes ∧ lanes ≤ s.lanes ∧ dst < s.vregs ∧ a < s.vregs ∧ b < s.vregs then
        some s else none
  | s, .emitTable idx _ => if idx < s.tables then some s else none
  | s, .tableLoad tbl _ dst => if tbl < s.tables ∧ dst < s.regs then some s else none
  | s, .setStatus _ => some { s with statusSet := true }
  | s, .buildOutput src =>
      if s.statusSet = true ∧ src.Fits s.mem then
        some { s with outputType := .bytes src.count } else none
  | s, .opaqueProcess spec body =>
      if spec.declaredSteps = body.stepBound ∧
          spec.declaredBytes = body.charges.moduleBytes then infer s body else none

/-- **Soundness.**  Everything the decision procedure accepts is derivable. -/
theorem infer_sound : ∀ (p : Plan) (s t : Sig), infer s p = some t → HasType s p t := by
  intro p
  induction p with
  | nop =>
    intro s t h
    rw [infer] at h
    cases h
    exact .nop s
  | seq a b iha ihb =>
    intro s t h
    rw [infer] at h
    cases hu : infer s a with
    | none => rw [hu] at h; exact absurd h (by simp)
    | some u =>
      rw [hu] at h
      exact .seq (iha s u hu) (ihb u t h)
  | classifyRaw v i u e ihv ihi ihu ihe =>
    intro s t h
    rw [infer, joinSig_eq_some, joinSig_eq_some, joinSig_eq_some] at h
    exact .classifyRaw (ihv s t h.1.1) (ihi s t h.1.2) (ihu s t h.2.1) (ihe s t h.2.2)
  | dispatchLayout r c g ihr ihc ihg =>
    intro s t h
    rw [infer, joinSig_eq_some, joinSig_eq_some] at h
    exact .dispatchLayout (ihr s t h.1) (ihc s t h.2.1) (ihg s t h.2.2)
  | branch co x y ihx ihy =>
    intro s t h
    rw [infer] at h
    by_cases hc : co.wellTyped s = true
    · rw [if_pos hc, joinSig_eq_some] at h
      exact .branch hc (ihx s t h.1) (ihy s t h.2)
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | pack src dst map w =>
    intro s t h
    rw [infer] at h
    by_cases hc : src.Fits s.mem ∧ dst.Fits s.scratch ∧ 0 < w
    · rw [if_pos hc] at h; cases h; exact .pack hc.1 hc.2.1 hc.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | unpack src dst map w =>
    intro s t h
    rw [infer] at h
    by_cases hc : src.Fits s.scratch ∧ dst.Fits s.mem ∧ 0 < w
    · rw [if_pos hc] at h; cases h; exact .unpack hc.1 hc.2.1 hc.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | storeReg dst map w src =>
    intro s t h
    rw [infer] at h
    by_cases hc : dst.Fits s.mem ∧ 0 < w ∧ src < s.regs ∧ 2 < s.regs
    · rw [if_pos hc] at h; cases h; exact .storeReg hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | loadReg dst src map w =>
    intro s t h
    rw [infer] at h
    by_cases hc : src.Fits s.mem ∧ 0 < w ∧ dst < s.regs ∧ 2 < s.regs
    · rw [if_pos hc] at h; cases h; exact .loadReg hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | loopNest axis body ih =>
    intro s t h
    rw [infer] at h
    by_cases hc : axis.indexReg < s.regs ∧ infer s body = some s
    · rw [if_pos hc] at h; cases h; exact .loopNest hc.1 (ih s s hc.2)
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | loopReg ir er map body ih =>
    intro s t h
    rw [infer] at h
    by_cases hc : ir < s.regs ∧ er < s.regs ∧ infer s body = some s
    · rw [if_pos hc] at h; cases h; exact .loopReg hc.1 hc.2.1 (ih s s hc.2.2)
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | tiled o ti ex body ih =>
    intro s t h
    rw [infer] at h
    by_cases hc : ti.Positive ∧ infer s body = some s
    · rw [if_pos hc] at h; cases h; exact .tiled hc.1 (ih s s hc.2)
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | reduce c acc lhs rhs =>
    intro s t h
    rw [infer] at h
    by_cases hc : acc < s.regs ∧ c.compatibleB = true ∧ lhs.Fits s.mem ∧ rhs.Fits s.mem
    · rw [if_pos hc] at h; cases h; exact .reduce hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | allocScratch n body ih =>
    intro s t h
    rw [infer] at h
    exact .allocScratch (ih _ t h)
  | setReg dst v =>
    intro s t h
    rw [infer] at h
    by_cases hc : dst < s.regs
    · rw [if_pos hc] at h; cases h; exact .setReg hc
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | scalarOp op dst a b =>
    intro s t h
    rw [infer] at h
    by_cases hc : dst < s.regs ∧ a < s.regs ∧ b < s.regs
    · rw [if_pos hc] at h; cases h; exact .scalarOp hc.1 hc.2.1 hc.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | vectorOp op lanes dst a b =>
    intro s t h
    rw [infer] at h
    by_cases hc : 0 < lanes ∧ lanes ≤ s.lanes ∧ dst < s.vregs ∧ a < s.vregs ∧ b < s.vregs
    · rw [if_pos hc] at h; cases h
      exact .vectorOp hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | emitTable idx data =>
    intro s t h
    rw [infer] at h
    by_cases hc : idx < s.tables
    · rw [if_pos hc] at h; cases h; exact .emitTable hc
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | tableLoad tbl idx dst =>
    intro s t h
    rw [infer] at h
    by_cases hc : tbl < s.tables ∧ dst < s.regs
    · rw [if_pos hc] at h; cases h; exact .tableLoad hc.1 hc.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | setStatus st =>
    intro s t h
    rw [infer] at h
    cases h
    exact .setStatus s st
  | buildOutput src =>
    intro s t h
    rw [infer] at h
    by_cases hc : s.statusSet = true ∧ src.Fits s.mem
    · rw [if_pos hc] at h; cases h; exact .buildOutput hc.1 hc.2
    · rw [if_neg hc] at h; exact absurd h (by simp)
  | opaqueProcess spec body ih =>
    intro s t h
    rw [infer] at h
    by_cases hc : spec.declaredSteps = body.stepBound ∧
        spec.declaredBytes = body.charges.moduleBytes
    · rw [if_pos hc] at h; exact .opaqueProcess hc.1 hc.2 (ih s t h)
    · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **Completeness.**  Everything derivable is accepted by the decision
procedure. -/
theorem infer_complete {s : Sig} {p : Plan} {t : Sig} (h : HasType s p t) :
    infer s p = some t := by
  induction h with
  | nop s => rfl
  | seq _ _ iha ihb => rw [infer, iha]; exact ihb
  | classifyRaw _ _ _ _ ihv ihi ihu ihe =>
    rw [infer, joinSig_eq_some, joinSig_eq_some, joinSig_eq_some]
    exact ⟨⟨ihv, ihi⟩, ihu, ihe⟩
  | dispatchLayout _ _ _ ihr ihc ihg =>
    rw [infer, joinSig_eq_some, joinSig_eq_some]
    exact ⟨ihr, ihc, ihg⟩
  | branch hco _ _ ihx ihy =>
    rw [infer, if_pos hco, joinSig_eq_some]
    exact ⟨ihx, ihy⟩
  | pack h1 h2 h3 => rw [infer, if_pos ⟨h1, h2, h3⟩]
  | unpack h1 h2 h3 => rw [infer, if_pos ⟨h1, h2, h3⟩]
  | storeReg h1 h2 h3 h4 => rw [infer, if_pos ⟨h1, h2, h3, h4⟩]
  | loadReg h1 h2 h3 h4 => rw [infer, if_pos ⟨h1, h2, h3, h4⟩]
  | loopNest h1 _ ih => rw [infer, if_pos ⟨h1, ih⟩]
  | loopReg h1 h2 _ ih => rw [infer, if_pos ⟨h1, h2, ih⟩]
  | tiled h1 _ ih => rw [infer, if_pos ⟨h1, ih⟩]
  | reduce h1 h2 h3 h4 => rw [infer, if_pos ⟨h1, h2, h3, h4⟩]
  | allocScratch _ ih => rw [infer]; exact ih
  | setReg h1 => rw [infer, if_pos h1]
  | scalarOp h1 h2 h3 => rw [infer, if_pos ⟨h1, h2, h3⟩]
  | vectorOp h1 h2 h3 h4 h5 => rw [infer, if_pos ⟨h1, h2, h3, h4, h5⟩]
  | emitTable h1 => rw [infer, if_pos h1]
  | tableLoad h1 h2 => rw [infer, if_pos ⟨h1, h2⟩]
  | setStatus s st => rfl
  | buildOutput h1 h2 => rw [infer, if_pos ⟨h1, h2⟩]
  | opaqueProcess h1 h2 _ ih => rw [infer, if_pos ⟨h1, h2⟩]; exact ih

/-- The judgment and the procedure are interchangeable. -/
theorem hasType_iff_infer (s : Sig) (p : Plan) (t : Sig) :
    HasType s p t ↔ infer s p = some t :=
  ⟨infer_complete, infer_sound p s t⟩

/-- The typing judgment is decidable. -/
instance instDecidableHasType (s : Sig) (p : Plan) (t : Sig) : Decidable (HasType s p t) :=
  decidable_of_iff _ (hasType_iff_infer s p t).symm

/-- Typing is deterministic: the output interface is a function of the input
interface and the plan. -/
theorem hasType_deterministic {s : Sig} {p : Plan} {t t' : Sig}
    (h : HasType s p t) (h' : HasType s p t') : t = t' := by
  have e1 := infer_complete h
  have e2 := infer_complete h'
  rw [e1] at e2
  exact Option.some.inj e2

/-! ## Properties of the resource transition -/

/-- A well-typed plan never shrinks the declared scratch. -/
theorem hasType_scratch_le {s : Sig} {p : Plan} {t : Sig} (h : HasType s p t) :
    s.scratch ≤ t.scratch := by
  induction h with
  | nop s => exact Nat.le_refl _
  | seq _ _ iha ihb => exact Nat.le_trans iha ihb
  | classifyRaw _ _ _ _ ihv _ _ _ => exact ihv
  | dispatchLayout _ _ _ ihr _ _ => exact ihr
  | branch _ _ _ ihx _ => exact ihx
  | pack => exact Nat.le_refl _
  | unpack => exact Nat.le_refl _
  | storeReg => exact Nat.le_refl _
  | loadReg => exact Nat.le_refl _
  | loopNest => exact Nat.le_refl _
  | loopReg => exact Nat.le_refl _
  | tiled => exact Nat.le_refl _
  | reduce => exact Nat.le_refl _
  | allocScratch _ ih => exact Nat.le_trans (Nat.le_add_right _ _) ih
  | setReg => exact Nat.le_refl _
  | scalarOp => exact Nat.le_refl _
  | vectorOp => exact Nat.le_refl _
  | emitTable => exact Nat.le_refl _
  | tableLoad => exact Nat.le_refl _
  | setStatus => exact Nat.le_refl _
  | buildOutput => exact Nat.le_refl _
  | opaqueProcess _ _ _ ih => exact ih

/-- A well-typed plan never changes the size of the register files, the lane
limit, the table count or the memory extent: the typing judgment fixes those
resources. -/
theorem hasType_fixed_resources {s : Sig} {p : Plan} {t : Sig} (h : HasType s p t) :
    t.regs = s.regs ∧ t.vregs = s.vregs ∧ t.lanes = s.lanes ∧ t.tables = s.tables ∧
      t.mem = s.mem ∧ t.inputType = s.inputType := by
  induction h with
  | nop s => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | seq _ _ iha ihb =>
    exact ⟨ihb.1.trans iha.1, ihb.2.1.trans iha.2.1, ihb.2.2.1.trans iha.2.2.1,
      ihb.2.2.2.1.trans iha.2.2.2.1, ihb.2.2.2.2.1.trans iha.2.2.2.2.1,
      ihb.2.2.2.2.2.trans iha.2.2.2.2.2⟩
  | classifyRaw _ _ _ _ ihv _ _ _ => exact ihv
  | dispatchLayout _ _ _ ihr _ _ => exact ihr
  | branch _ _ _ ihx _ => exact ihx
  | pack => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | unpack => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | storeReg => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | loadReg => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | loopNest => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | loopReg => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | tiled => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | reduce => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | allocScratch _ ih => exact ih
  | setReg => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | scalarOp => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | vectorOp => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | emitTable => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | tableLoad => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | setStatus => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | buildOutput => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | opaqueProcess _ _ _ ih => exact ih

/-- The opaque-process rule is not a trust rule: a well-typed opaque node's
declared certificate is exactly the value recomputed from its retained body. -/
theorem opaqueProcess_certificate_exact {s t : Sig} {spec : OpaqueSpec} {body : Plan}
    (h : HasType s (.opaqueProcess spec body) t) :
    spec.declaredSteps = body.stepBound ∧
      spec.declaredBytes = body.charges.moduleBytes := by
  cases h with
  | opaqueProcess h1 h2 _ => exact ⟨h1, h2⟩

/-! ## Legacy signature-indexed typed plans -/

/-- A plan together with its internal signature-indexed typing derivation.

This is the compiler-independent typing object used by the plan metatheory.  It
is deliberately not the public `CheckedPlan P G`: a pair of internal signatures
does not bind a plan to the released Wasm profile, GEMM problem, ABI, or Core
representability bounds. -/
structure TypedPlan (s t : Sig) where
  plan : Plan
  typed : HasType s plan t

namespace TypedPlan

variable {s t : Sig}

/-- The certified cost of a checked plan (SPEC §11.3). -/
def certifiedCost (c : TypedPlan s t) : Nat := c.plan.certifiedCost

/-- The resource bound of a checked plan (SPEC §11.3). -/
def resourceBound (c : TypedPlan s t) : Nat := c.plan.stepBound

/-- The behaviour of a checked plan. -/
def eval (c : TypedPlan s t) : Machine → Machine := Eval c.plan

/-- Building a checked plan by running the decision procedure. -/
def check? (s : Sig) (p : Plan) (t : Sig) : Option (TypedPlan s t) :=
  if h : HasType s p t then some ⟨p, h⟩ else none

theorem check?_isSome_iff (s : Sig) (p : Plan) (t : Sig) :
    (check? s p t).isSome = true ↔ HasType s p t := by
  unfold check?
  by_cases h : HasType s p t <;> simp [h]

end TypedPlan

/-! ## Public profile/problem-indexed checked plans

The public carrier is constructed only after an independent, executable source
check has established the finite-width obligations needed by a wasm32 Core
compiler.  The check is stated entirely over GNAF source data, profile limits,
and problem resource constants.  In particular it does not mention an emitted
module, the binary encoder, a run, an observation, or compiler correctness.
-/

namespace IndexMap

/-- Largest byte coefficient generated from an affine source map by the
scalar Core lowering.  `Machine.mem` already is the ABI byte image. -/
def coreImmediateCeiling (map : IndexMap) : Nat :=
  max map.c0 (max map.cb (max map.ci map.cj))

end IndexMap

namespace RegionRef

/-- Largest fixed byte immediate generated from a source region. -/
def coreImmediateCeiling (region : RegionRef) : Nat :=
  max region.base (max region.count region.limit)

end RegionRef

namespace Cond

/-- Largest source numeral occurring in a decidable branch condition. -/
def coreImmediateCeiling : Cond → Nat
  | .statusIs status => status.code
  | .regEq reg value | .regLt reg value => max reg value
  | .scratchAtLeast bytes => bytes

end Cond

namespace Plan

/-- Maximum of a list of natural numerals, with zero for the empty list. -/
def listCeiling (values : List Nat) : Nat := values.foldl Nat.max 0

/-- Maximum number of cells required by any one source-level code/data table. -/
def tableWords : Plan → Nat
  | .nop => 0
  | .seq first second => max first.tableWords second.tableWords
  | .classifyRaw valid invalid unsupported exhausted =>
      max (max valid.tableWords invalid.tableWords)
        (max unsupported.tableWords exhausted.tableWords)
  | .dispatchLayout rowMajor colMajor general =>
      max rowMajor.tableWords (max colMajor.tableWords general.tableWords)
  | .branch _ onTrue onFalse => max onTrue.tableWords onFalse.tableWords
  | .pack _ _ _ _ | .unpack _ _ _ _ | .storeReg _ _ _ _ |
      .loadReg _ _ _ _ | .reduce _ _ _ _ | .setReg _ _ |
      .scalarOp _ _ _ _ | .vectorOp _ _ _ _ _ | .setStatus _ |
      .buildOutput _ => 0
  | .loopNest _ body | .loopReg _ _ _ body | .tiled _ _ _ body |
      .allocScratch _ body | .opaqueProcess _ body => body.tableWords
  | .emitTable _ data => data.length
  | .tableLoad _ index _ => index + 1

/-- A source-only upper bound on every fixed numeral the direct Core lowering
may emit for one plan node.  Recursive branches take maxima; table payloads
include their contents and their exact fixed-address product. -/
def coreImmediateCeiling : Plan → Nat
  | .nop => 0
  | .seq first second => max first.coreImmediateCeiling second.coreImmediateCeiling
  | .classifyRaw valid invalid unsupported exhausted =>
      max valid.coreImmediateCeiling
        (max invalid.coreImmediateCeiling
          (max unsupported.coreImmediateCeiling exhausted.coreImmediateCeiling))
  | .dispatchLayout rowMajor colMajor general =>
      max rowMajor.coreImmediateCeiling
        (max colMajor.coreImmediateCeiling general.coreImmediateCeiling)
  | .branch condition onTrue onFalse =>
      max condition.coreImmediateCeiling
        (max onTrue.coreImmediateCeiling onFalse.coreImmediateCeiling)
  | .pack src dst map width | .unpack src dst map width =>
      max width (max src.coreImmediateCeiling
        (max dst.coreImmediateCeiling map.coreImmediateCeiling))
  | .storeReg dst map width src =>
      max src (max width (max dst.coreImmediateCeiling map.coreImmediateCeiling))
  | .loadReg dst src map width =>
      max dst (max width (max src.coreImmediateCeiling map.coreImmediateCeiling))
  | .loopNest axis body =>
      max axis.indexReg
        (max axis.extent (max axis.map.coreImmediateCeiling body.coreImmediateCeiling))
  | .loopReg indexReg extentReg map body =>
      max indexReg (max extentReg
        (max map.coreImmediateCeiling body.coreImmediateCeiling))
  | .tiled _ tiling extents body =>
      max (tiling.totalTiles extents.m extents.n extents.k)
        (max tiling.mBlock (max tiling.nBlock (max tiling.kBlock
          (max extents.m (max extents.n (max extents.k body.coreImmediateCeiling))))))
  | .reduce _ acc lhs rhs =>
      max acc (max lhs.coreImmediateCeiling rhs.coreImmediateCeiling)
  | .allocScratch bytes body => max bytes body.coreImmediateCeiling
  | .setReg dst value => max dst value
  | .scalarOp _ dst lhs rhs => max dst (max lhs rhs)
  | .vectorOp _ lanes dst lhs rhs => max lanes (max dst (max lhs rhs))
  | .emitTable index data =>
      max index (max data.length (listCeiling data))
  | .tableLoad table index dst => max table (max index dst)
  | .setStatus status => status.code
  | .buildOutput src => src.coreImmediateCeiling
  | .opaqueProcess spec body =>
      max spec.processId
        (max spec.declaredSteps (max spec.declaredBytes body.coreImmediateCeiling))

/-- Byte extent of the compiler's closed linear-memory layout, computed from
source resources only.  There is no clamp or modular reduction. -/
def coreLayoutBytes (s : Sig) (plan : Plan) : Nat :=
  s.mem + 8 * ((s.scratch + plan.charges.scratchPeak) +
    s.tables * plan.tableWords) + 12

/-- Exact page count for the source layout. -/
def coreLayoutPages (s : Sig) (plan : Plan) : Nat :=
  Wasm.pagesFor (coreLayoutBytes s plan)

/-- Source-only instruction-tree budget for the direct Core lowering.  Its
recursion mirrors only the *shape* of the plan: fixed constants cover the
closed classification/layout/loop templates, while the table case accounts
for every literal cell.  `GNAF/CompileEncoding.lean` proves the emitted Core
instruction tree fits this independently computed budget. -/
def codeBudget : Plan → Nat
  | .nop => 0
  | .seq first second => first.codeBudget + second.codeBudget
  | .classifyRaw valid invalid unsupported exhausted =>
      4096 + valid.codeBudget + invalid.codeBudget +
        unsupported.codeBudget + exhausted.codeBudget
  | .dispatchLayout rowMajor colMajor general =>
      2048 + rowMajor.codeBudget + colMajor.codeBudget + general.codeBudget
  | .branch _ onTrue onFalse => 128 + onTrue.codeBudget + onFalse.codeBudget
  | .pack _ _ _ _ | .unpack _ _ _ _ => 256
  | .storeReg _ _ _ _ | .loadReg _ _ _ _ => 128
  | .loopNest _ body | .loopReg _ _ _ body | .tiled _ _ _ body =>
      256 + body.codeBudget
  | .reduce _ _ _ _ => 256
  | .allocScratch _ body | .opaqueProcess _ body => body.codeBudget
  | .setReg _ _ => 16
  | .scalarOp _ _ _ _ => 128
  | .vectorOp _ _ _ _ _ => 16
  | .emitTable _ data => 16 * (data.length + 1)
  | .tableLoad _ _ _ => 32
  | .setStatus _ => 16
  | .buildOutput _ => 32

/-- Conservative source-only byte budget for the direct Core lowering.  The
factor covers the longest fixed-width encoding emitted per charged source node;
the constant covers the closed type/export/section envelope. -/
def coreModuleByteBudget (plan : Plan) : Nat :=
  32 * (plan.codeBudget + 4) + 4096

/-- Independent decidable certificate consumed by the public Core compiler.
It checks all fixed immediates, the exact unwrapped layout, local/index spaces,
the profile's module and memory limits, and the problem's resource contract. -/
def coreRepresentable (P : Wasm.Profile) (G : Gemm.Problem P)
    (s : Sig) (plan : Plan) : Bool :=
  decide
    (max (plan.coreImmediateCeiling)
        (max (3 + s.regs + plan.depth) (plan.coreLayoutBytes s)) < 2 ^ 32 ∧
      plan.coreLayoutPages s ≤ P.body.maxPages ∧
      plan.coreLayoutPages s ≤ G.body.resources.maxPages ∧
      s.regs + plan.depth + 2 ≤ P.body.limits.maxLocals ∧
      plan.coreModuleByteBudget < 2 ^ 32 ∧
      plan.coreModuleByteBudget ≤ P.body.limits.maxModuleBytes ∧
      plan.charges.dataBytes ≤ G.body.resources.maxInvocationBytes ∧
      s.tables * plan.tableWords ≤ G.body.resources.maxTableElements)

/-- The arithmetic fragment whose direct amended-Core lowering is implemented
with exact `i32` modular behavior.  Other released arithmetic contracts stay
in the source language but cannot cross the checked compiler boundary yet. -/
def coreScalarI32Supported (contract : ArithmeticContract) : Bool :=
  contract.mode == .modular && contract.accumulator == .u32

/-- Scalar operations whose unbounded-`Nat` source equation agrees with the
Core `i32` lowering on values represented by locals.  Addition and
multiplication are intentionally absent: the source operations are unbounded,
whereas Core wraps them modulo `2^32`. -/
def coreScalarOpSupported : ScalarOp → Bool
  | .sub | .max | .min => true
  | .add | .mul => false

/-- Independently checked support predicate for the direct amended-Core
lowering.  It is deliberately a predicate on the complete profile/problem/
interface/plan input to the checker.  The currently admitted fragment is the
straight-line scalar/status path: immediate register writes, non-wrapping
scalar operations, scratch allocation wrappers, status construction, and
source-private output-view construction.  `buildOutput` changes only
`Machine.out`; `GNAF.Accepts` observes the returned status and complete source
memory image, so its lowering is the proved empty observational projection.
Control, raw-byte, table, memory-transfer, reduction, and vector nodes are
rejected until their independent execution simulations are proved.  The plan
language itself remains unchanged, and widening this decision procedure does
not change the artifact type. -/
def coreSupported (_P : Wasm.Profile) (_G : Gemm.Problem _P)
    (_s : Sig) : Plan → Bool
  | .nop => true
  | .seq first second =>
      coreSupported _P _G _s first && coreSupported _P _G _s second
  | .classifyRaw _ _ _ _ | .dispatchLayout _ _ _ => false
  | .branch _ _ _ | .loopNest _ _ | .loopReg _ _ _ _ | .tiled _ _ _ _ => false
  | .allocScratch _ body | .opaqueProcess _ body => coreSupported _P _G _s body
  | .setReg _ _ | .setStatus _ | .buildOutput _ => true
  | .scalarOp operation _ _ _ => coreScalarOpSupported operation
  | .pack _ _ _ _ | .unpack _ _ _ _ | .storeReg _ _ _ _ |
      .loadReg _ _ _ _ | .reduce _ _ _ _ | .vectorOp _ _ _ _ _ |
      .emitTable _ _ | .tableLoad _ _ _ => false

end Plan

/-- **SPEC §11.3.**  A compile-ready plan is indexed by the exact public
profile and GEMM problem and carries only independently checked source facts.
No compiler result, run, observation, cost equality, or semantic conclusion is
stored in this structure. -/
structure CheckedPlan (P : Wasm.Profile) (G : Gemm.Problem P) where
  inputSig : Sig
  outputSig : Sig
  plan : Plan
  typed : HasType inputSig plan outputSig
  coreRepresentable : plan.coreRepresentable P G inputSig = true
  coreSupported : plan.coreSupported P G inputSig = true

namespace CheckedPlan

variable {P : Wasm.Profile} {G : Gemm.Problem P}

/-- The exact static instruction-tree budget consumed by `compile_resources`.
Dynamic public-Core execution bounds are stated separately over relational
prefixes; this value does not conflate source interpreter steps with Core
reduction steps. -/
def resourceBound (checked : CheckedPlan P G) : Nat := checked.plan.codeBudget + 4

/-- Number of status-local replacement steps emitted by the currently admitted
straight-line lowering.  Register/scalar nodes are observationally dead in
this fragment; status assignments are retained in source order. -/
def compiledStatusSteps : Plan → Nat
  | .seq first second => compiledStatusSteps first + compiledStatusSteps second
  | .allocScratch _ body | .opaqueProcess _ body => compiledStatusSteps body
  | .setStatus _ => 1
  | _ => 0

/-- Exact byte extent of the compiler's initial private/public memory layout,
stated purely from checked source data. -/
def compiledInitialMemoryBytes (checked : CheckedPlan P G) : Nat :=
  checked.inputSig.mem +
    8 * (checked.inputSig.scratch + checked.plan.charges.scratchPeak) +
    8 * (checked.inputSig.tables * checked.plan.tableWords) + 12

/-- Exact initial page count of the emitted module, before the Harness grows
the public raw-input window. -/
def compiledInitialPages (checked : CheckedPlan P G) : Nat :=
  Wasm.pagesFor checked.compiledInitialMemoryBytes

/-- Exact number of compiler-declared locals beyond the two ABI parameters. -/
def compiledDeclaredLocals (checked : CheckedPlan P G) : Nat :=
  checked.inputSig.regs + checked.plan.depth + 2

/-- Exact source-computable charge of the admitted compiler image on one raw
invocation.  This is deliberately independent of an evaluator result: it is a
closed structural formula over the checked source, the released profile cost
table, and the lawful raw window.  Cumulative coordinates count the six
deterministic initialization subevents and the emitted Harness/Core path;
peak coordinates are the maxima of the corresponding concrete configuration
sequence. -/
def certifiedCost (checked : CheckedPlan P G) (raw : G.RawInvocation) :
    Cost.DynamicVector :=
  let statusSteps := compiledStatusSteps checked.plan
  let initialPages := checked.compiledInitialPages
  let targetPages := Wasm.pagesFor (raw.body.ptr.toNat + raw.body.len.toNat)
  let grownPages := targetPages - initialPages
  { instantiationSteps := 6
    dispatchSteps := 5
    preparationSteps := P.costTableBody.installationPreparationUnit
    wasmRuleSteps := P.costTableBody.ruleStepUnit * (statusSteps + 14)
    scalarOps := 1
    vectorLaneOps := 0
    bytesRead := 0
    bytesWritten :=
      P.costTableBody.installedByteWriteUnit * raw.body.len.toNat
    memoryGrowPages := grownPages
    tableElementsAllocated := 0
    gcObjectsAllocated := 0
    gcBytesInitialized := 0
    peakStackValues :=
      checked.compiledDeclaredLocals + 4 + max statusSteps 1
    peakPages := initialPages + grownPages
    peakGcLiveBytes := 0
    outputBytes := 4 }

/-- The independently defined plan-machine behavior retained by a checked
source value. -/
def eval (checked : CheckedPlan P G) : Machine → Machine := Eval checked.plan

/-- Execute both independent decision procedures.  A failed source typing or
Core-representability check produces no public checked plan. -/
def check? (P : Wasm.Profile) (G : Gemm.Problem P)
    (input : Sig) (plan : Plan) (output : Sig) : Option (CheckedPlan P G) :=
  if typed : HasType input plan output then
    if represented : plan.coreRepresentable P G input = true then
      if supported : plan.coreSupported P G input = true then
        some ⟨input, output, plan, typed, represented, supported⟩
      else none
    else none
  else none

theorem check?_isSome_iff (P : Wasm.Profile) (G : Gemm.Problem P)
    (input : Sig) (plan : Plan) (output : Sig) :
    (check? P G input plan output).isSome = true ↔
      HasType input plan output ∧ plan.coreRepresentable P G input = true ∧
        plan.coreSupported P G input = true := by
  unfold check?
  by_cases typed : HasType input plan output
  · simp only [typed, dite_true, true_and]
    by_cases represented : plan.coreRepresentable P G input = true
    · simp only [represented, dite_true, true_and]
      by_cases supported : plan.coreSupported P G input = true <;>
        simp [supported]
    · simp [represented]
  · simp [typed]

end CheckedPlan

/-! ## Type safety -/

namespace Machine

/-- A configuration conforms to an interface when its private stores have the
declared sizes, its public memory contains at least the declared source
extent, and scratch contains at least its declared extent.  Public memory is
a lower bound because the ABI Harness may grow it to retain a lawful raw
window above the module's small initial minimum. -/
def Conforms (m : Machine) (s : Sig) : Prop :=
  m.regs.length = s.regs ∧ m.vregs.length = s.vregs ∧ s.mem ≤ m.mem.length ∧
    m.tables.length = s.tables ∧ s.scratch ≤ m.scratch.length

theorem conforms_withReg {m : Machine} {s : Sig} (h : m.Conforms s) (r v : Nat) :
    (m.withReg r v).Conforms s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by simpa using h1, h2, h3, h4, h5⟩

end Machine

/-- Conformance is preserved by a loop whose body preserves it. -/
theorem runLoop_conforms {f : Machine → Machine} {s : Sig}
    (hf : ∀ m, m.Conforms s → (f m).Conforms s) (r : Nat) :
    ∀ (n i : Nat) (m : Machine), m.Conforms s → (Plan.runLoop f r n i m).Conforms s := by
  intro n
  induction n with
  | zero => intro i m h; exact h
  | succ n ih =>
    intro i m h
    rw [Plan.runLoop_succ]
    exact ih (i + 1) _ (hf _ (Machine.conforms_withReg h r i))

/-- **Type safety.**  A well-typed plan maps configurations conforming to its
input interface to configurations conforming to its output interface. -/
theorem hasType_preservation {s : Sig} {p : Plan} {t : Sig} (h : HasType s p t) :
    ∀ m : Machine, m.Conforms s → (p.eval m).Conforms t := by
  induction h with
  | nop s => intro m hm; exact hm
  | seq _ _ iha ihb => intro m hm; exact ihb _ (iha m hm)
  | classifyRaw _ _ _ _ ihv ihi ihu ihe =>
    intro m hm
    rw [Plan.eval_classifyRaw]
    cases m.classify
    · exact ihv m hm
    · exact ihi m hm
    · exact ihu m hm
    · exact ihe m hm
  | dispatchLayout _ _ _ ihr ihc ihg =>
    intro m hm
    rw [Plan.eval_dispatchLayout]
    cases m.layoutClass
    · exact ihr m hm
    · exact ihc m hm
    · exact ihg m hm
  | @branch s t co x y _ _ _ ihx ihy =>
    intro m hm
    rw [Plan.eval_branch]
    by_cases hc : co.eval m = true
    · rw [if_pos hc]; exact ihx m hm
    · rw [if_neg hc]; exact ihy m hm
  | @pack s src dst map w _ _ _ =>
    intro m hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    refine ⟨h1, h2, h3, h4, ?_⟩
    show s.scratch ≤ (packedScratch m src dst map).length
    rw [packedScratch_length]
    exact h5
  | @unpack s src dst map w _ _ _ =>
    intro m hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    refine ⟨h1, h2, ?_, h4, h5⟩
    show s.mem ≤ (unpackedMem m src dst map).length
    rw [unpackedMem_length]
    exact h3
  | @storeReg s dst map w src _ _ _ _ =>
    intro m hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    refine ⟨h1, h2, ?_, h4, h5⟩
    show s.mem ≤ (storedRegMem m dst map w src).length
    rw [storedRegMem_length]
    exact h3
  | @loadReg s dst src map w _ _ _ _ =>
    intro m hm
    exact Machine.conforms_withReg hm _ _
  | @loopNest s axis body _ _ ih =>
    intro m hm
    rw [Plan.eval_loopNest]
    exact runLoop_conforms ih axis.indexReg axis.extent 0 m hm
  | @loopReg s ir er map body _ _ _ ih =>
    intro m hm
    rw [eval_loopReg]
    exact runLoop_conforms ih ir (Nat.min (m.reg er) loopRegMaxTrips) 0 m hm
  | @tiled s o ti ex body _ _ ih =>
    intro m hm
    rw [Plan.eval_tiled]
    exact runLoop_conforms ih 0 (ti.totalTiles ex.m ex.n ex.k) 0 m hm
  | @reduce s c acc lhs rhs _ _ _ _ =>
    intro m hm
    rw [Plan.eval]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    split
    · exact ⟨h1, h2, h3, h4, h5⟩
    · exact Machine.conforms_withReg ⟨h1, h2, h3, h4, h5⟩ _ _
  | @allocScratch s t n body _ ih =>
    intro m hm
    rw [Plan.eval_allocScratch]
    refine ih _ ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    refine ⟨h1, h2, h3, h4, ?_⟩
    show s.scratch + n ≤ (m.scratch ++ List.replicate n 0).length
    simp only [List.length_append, List.length_replicate]
    omega
  | setReg _ => intro m hm; exact Machine.conforms_withReg hm _ _
  | scalarOp _ _ _ => intro m hm; exact Machine.conforms_withReg hm _ _
  | @vectorOp s op lanes dst a b _ _ _ _ _ =>
    intro m hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    exact ⟨h1, by simpa using h2, h3, h4, h5⟩
  | @emitTable s idx data hidx =>
    intro m hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    exact ⟨h1, h2, h3, by simpa using h4, h5⟩
  | tableLoad _ _ => intro m hm; exact Machine.conforms_withReg hm _ _
  | setStatus s st => intro m hm; exact hm
  | buildOutput _ _ => intro m hm; exact hm
  | opaqueProcess _ _ _ ih => intro m hm; exact ih m hm

/-- Type safety for checked plans. -/
theorem TypedPlan.preservation {s t : Sig} (c : TypedPlan s t) (m : Machine)
    (hm : m.Conforms s) : (c.eval m).Conforms t :=
  hasType_preservation c.typed m hm

end WasmGemmGnaf.GNAF
