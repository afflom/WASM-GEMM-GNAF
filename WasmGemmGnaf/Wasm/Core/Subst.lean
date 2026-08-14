/-
  Wasm/Core/Subst.lean --- type substitution, rolling, unrolling and expansion
  for the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every definition below transcribes a `def` of

      vendor/wasm-spec/specification/wasm-3.0/1.2-syntax.types.spectec

  at the pinned commit, sections "Substitution" and "Rolling & unrolling".

  WHY THIS FILE EXISTS SEPARATELY FROM THE TYPING RULES.  The declarative
  judgment of `2.*-validation.*.spectec` is an inductive relation, but several of
  its premises are equations between the results of SpecTec *functions* --
  `$unrolldt`, `$expanddt`, `$clos_deftype`, `$rolldt`.  Those are total (or
  explicitly partial) computable functions in the source and are transcribed as
  such here.  They are NOT a validator: nothing below decides any judgment.  The
  typing relation imports them exactly where the pinned rules name them.

  PARTIALITY.  Where the source gives equations for only some constructors
  (`$as_deftype`, `$unrolldt`, `$expanddt`, `$unrollht`) the Lean function is
  `Option`-valued, so the missing equations become `none` rather than a junk
  value.  A `-- if $f(x) = y` premise then reads `f x = some y`, which is
  exactly the source's meaning: the premise holds only where the equation
  applies.
-/
import WasmGemmGnaf.Wasm.Core.Types

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- A `typeidx` from a natural number.

The source writes `$(x + i)` in `$rollrt` and `(_IDX i)^(i<n)` in
`$subst_all_*` with unbounded natural arithmetic, while the sort
`typeidx = u32` is bounded.  The transcription therefore reduces modulo
`2^32`.  Every use in the pinned rules has the argument below `2^32` (it is a
type-section index, and `list(...)` bounds a module's type section by `2^32`),
so the reduction is unreachable on a well-formed module. -/
def TypeIdx.ofNat (n : Nat) : TypeIdx := ⟨n % 2 ^ 32, Nat.mod_lt _ (two_pow_pos 32)⟩

/-- `typevar` read as a `typeuse`: `typeuse` has `_IDX typeidx` in its `/syn`
fragment and `REC n` in its `/sem` fragment, which are exactly the two cases of
`typevar`. -/
def TypeVar.toTypeUse : TypeVar → TypeUse
  | .idx x => .idx x
  | .recv n => .recu n

/-- The `typevar` reading of a `typeuse`, where there is one. -/
def TypeUse.toTypeVar? : TypeUse → Option TypeVar
  | .idx x => some (.idx x)
  | .recu n => some (.recv n)
  | .defd _ => none

/-! ## Substitution -/

/-- `def $subst_typevar(typevar, typevar*, typeuse*) : typeuse`:

    $subst_typevar(tv, eps, eps) = tv
    $subst_typevar(tv, tv_1 tv'*, tu_1 tu'*) = tu_1                           -- if tv = tv_1
    $subst_typevar(tv, tv_1 tv'*, tu_1 tu'*) = $subst_typevar(tv, tv'*, tu'*) -- otherwise

The source gives no equation for lists of unequal length; the transcription
stops and returns the variable unchanged, which agrees with the source on every
argument the source defines. -/
def substTypeVar : TypeVar → List TypeVar → List TypeUse → TypeUse
  | tv, tv₁ :: tvs, tu₁ :: tus => if tv = tv₁ then tu₁ else substTypeVar tv tvs tus
  | tv, _, _ => tv.toTypeUse

/-! ### Exact lookup laws for rolling and unrolling

The validation relation supplies a non-wrapping bound for every recursive type
group.  Under that bound, the parallel substitutions used by `rollRt` and
`unrollRt` have the ordinary interval-lookup behavior suggested by the source
notation.  These lemmas make that fact reusable by validation and runtime
type-origin proofs; none of them decides a typing judgment. -/

/-- `TypeIdx.ofNat` is exact, rather than merely congruent modulo `2^32`, on
the source type-index range. -/
theorem TypeIdx.ofNat_val_of_lt (n : Nat) (h : n < 2 ^ 32) :
    (TypeIdx.ofNat n).val = n := by
  simp [TypeIdx.ofNat, Nat.mod_eq_of_lt h]

/-- Lookup in a non-wrapping slice of the rolling substitution. -/
private theorem substTypeVar_rollRange' (x y : TypeIdx) (start n : Nat)
    (hbound : x.val + start + n ≤ 2 ^ 32) :
    substTypeVar (.idx y)
      ((List.range' start n).map
        (fun j => TypeVar.idx (TypeIdx.ofNat (x.val + j))))
      ((List.range' start n).map (fun j => TypeUse.recu j)) =
      if x.val + start ≤ y.val ∧ y.val < x.val + start + n then
        .recu (y.val - x.val)
      else .idx y := by
  induction n generalizing start with
  | zero =>
      rw [if_neg (by omega)]
      rfl
  | succ n ih =>
      rw [List.range'_succ]
      simp only [List.map_cons, substTypeVar]
      have hhead : x.val + start < 2 ^ 32 := by omega
      have hval : (TypeIdx.ofNat (x.val + start)).val = x.val + start :=
        TypeIdx.ofNat_val_of_lt _ hhead
      by_cases heq : y.val = x.val + start
      · have hidx : y = TypeIdx.ofNat (x.val + start) :=
          Subtype.ext (by simpa [hval] using heq)
        rw [if_pos (by simp [hidx])]
        simp [heq]
      · have hidx : y ≠ TypeIdx.ofNat (x.val + start) := by
          intro h
          apply heq
          simpa [hval] using congrArg Subtype.val h
        rw [if_neg (by simpa using hidx)]
        rw [ih (start := start + 1) (by omega)]
        by_cases hrange :
            x.val + (start + 1) ≤ y.val ∧
              y.val < x.val + (start + 1) + n
        · rw [if_pos hrange, if_pos (by omega)]
        · rw [if_neg hrange, if_neg (by omega)]

/-- The rolling substitution turns exactly the indices occupied by the current
non-wrapping group into their corresponding `REC` variables. -/
theorem substTypeVar_rollVars (x y : TypeIdx) (n : Nat)
    (hbound : x.val + n ≤ 2 ^ 32) :
    substTypeVar (.idx y)
      ((List.range n).map
        (fun j => TypeVar.idx (TypeIdx.ofNat (x.val + j))))
      ((List.range n).map (fun j => TypeUse.recu j)) =
      if x.val ≤ y.val ∧ y.val < x.val + n then
        .recu (y.val - x.val)
      else .idx y := by
  rw [List.range_eq_range']
  simpa using substTypeVar_rollRange' x y 0 n (by omega)

/-- An ordinary type index is untouched by the recursive-variable substitution
used by `unrollRt`. -/
private theorem substTypeVar_unrollIdxRange' (y : TypeIdx) (qt : RecType)
    (start n : Nat) :
    substTypeVar (.idx y)
      ((List.range' start n).map TypeVar.recv)
      ((List.range' start n).map (fun j => TypeUse.defd (.defd qt j))) =
      .idx y := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      rw [List.range'_succ]
      simp only [List.map_cons, substTypeVar, reduceCtorEq, ↓reduceIte]
      exact ih (start + 1)

theorem substTypeVar_unrollIdxVars (y : TypeIdx) (n : Nat) (qt : RecType) :
    substTypeVar (.idx y)
      ((List.range n).map TypeVar.recv)
      ((List.range n).map (fun j => TypeUse.defd (.defd qt j))) =
      .idx y := by
  rw [List.range_eq_range']
  exact substTypeVar_unrollIdxRange' y qt 0 n

/-- Lookup in a slice of the recursive-variable substitution used by
`unrollRt`. -/
private theorem substTypeVar_unrollRecRange' (j start n : Nat) (qt : RecType) :
    substTypeVar (.recv j)
      ((List.range' start n).map TypeVar.recv)
      ((List.range' start n).map (fun k => TypeUse.defd (.defd qt k))) =
      if start ≤ j ∧ j < start + n then .defd (.defd qt j) else .recu j := by
  induction n generalizing start with
  | zero =>
      rw [if_neg (by omega)]
      rfl
  | succ n ih =>
      rw [List.range'_succ]
      simp only [List.map_cons, substTypeVar]
      by_cases heq : j = start
      · subst j
        rw [if_pos rfl]
        simp
      · rw [if_neg (by simpa using heq)]
        rw [ih (start + 1)]
        by_cases hrange : start + 1 ≤ j ∧ j < start + 1 + n
        · rw [if_pos hrange, if_pos (by omega)]
        · rw [if_neg hrange, if_neg (by omega)]

/-- `unrollRt` closes exactly the in-range `REC` variables with the matching
member of its own recursive group. -/
theorem substTypeVar_unrollRecVars (j n : Nat) (qt : RecType) :
    substTypeVar (.recv j)
      ((List.range n).map TypeVar.recv)
      ((List.range n).map (fun k => TypeUse.defd (.defd qt k))) =
      if j < n then .defd (.defd qt j) else .recu j := by
  rw [List.range_eq_range']
  simpa using substTypeVar_unrollRecRange' j 0 n qt

/-- `def $minus_recs(typevar*, typeuse*) : (typevar*, typeuse*)`: drop every
`REC n` variable, together with the `typeuse` opposite it. -/
def minusRecs : List TypeVar → List TypeUse → List TypeVar × List TypeUse
  | .recv _ :: tvs, _ :: tus => minusRecs tvs tus
  | .idx x :: tvs, tu₁ :: tus =>
      let p := minusRecs tvs tus
      (.idx x :: p.1, tu₁ :: p.2)
  | _, _ => ([], [])

mutual

/-- `def $subst_typeuse(typeuse, typevar*, typeuse*) : typeuse`. -/
def substTypeUse (tu : TypeUse) (tvs : List TypeVar) (tus : List TypeUse) : TypeUse :=
  match tu with
  | .idx x => substTypeVar (.idx x) tvs tus
  | .recu n => substTypeVar (.recv n) tvs tus
  | .defd dt => .defd (substDefType dt tvs tus)

/-- `def $subst_deftype((_DEF qt i), tv*, tu*) = _DEF $subst_rectype(qt, tv*, tu*) i`. -/
def substDefType (dt : DefType) (tvs : List TypeVar) (tus : List TypeUse) : DefType :=
  match dt with
  | .defd qt i => .defd (substRecType qt tvs tus) i

/-- `def $subst_rectype((REC st*), tv*, tu*) = REC $subst_subtype(st, tv'*, tu'*)*
    -- if (tv'*, tu'*) = $minus_recs(tv*, tu*)`.

The `REC` variables are dropped before descending, because inside a `rectype`
they are bound by the group itself. -/
def substRecType (qt : RecType) (tvs : List TypeVar) (tus : List TypeUse) : RecType :=
  match qt with
  | .recr sts =>
      let p := minusRecs tvs tus
      .recr (substSubTypes sts p.1 p.2)

/-- `$subst_subtype` mapped over a `subtype*`. -/
def substSubTypes (sts : SubTypes) (tvs : List TypeVar) (tus : List TypeUse) : SubTypes :=
  match sts with
  | .nil => .nil
  | .cons st rest => .cons (substSubType st tvs tus) (substSubTypes rest tvs tus)

/-- `def $subst_subtype((SUB final? tu'* ct), tv*, tu*)
    = SUB final? $subst_typeuse(tu', tv*, tu*)* $subst_comptype(ct, tv*, tu*)`. -/
def substSubType (st : SubType) (tvs : List TypeVar) (tus : List TypeUse) : SubType :=
  match st with
  | .sub fin sups ct => .sub fin (substTypeUses sups tvs tus) (substCompType ct tvs tus)

/-- `$subst_typeuse` mapped over a `typeuse*`. -/
def substTypeUses (sups : TypeUses) (tvs : List TypeVar) (tus : List TypeUse) : TypeUses :=
  match sups with
  | .nil => .nil
  | .cons tu rest => .cons (substTypeUse tu tvs tus) (substTypeUses rest tvs tus)

/-- `def $subst_comptype`, all three equations. -/
def substCompType (ct : CompType) (tvs : List TypeVar) (tus : List TypeUse) : CompType :=
  match ct with
  | .struct fts => .struct (substFieldTypes fts tvs tus)
  | .array ft => .array (substFieldType ft tvs tus)
  | .func dom cod => .func (substValTypes dom tvs tus) (substValTypes cod tvs tus)

/-- `$subst_fieldtype` mapped over a `fieldtype*`. -/
def substFieldTypes (fts : FieldTypes) (tvs : List TypeVar) (tus : List TypeUse) : FieldTypes :=
  match fts with
  | .nil => .nil
  | .cons ft rest => .cons (substFieldType ft tvs tus) (substFieldTypes rest tvs tus)

/-- `def $subst_fieldtype((mut? zt), tv*, tu*) = mut? $subst_storagetype(zt, tv*, tu*)`. -/
def substFieldType (ft : FieldType) (tvs : List TypeVar) (tus : List TypeUse) : FieldType :=
  match ft with
  | .mk m zt => .mk m (substStorageType zt tvs tus)

/-- `def $subst_storagetype`, both equations. -/
def substStorageType (zt : StorageType) (tvs : List TypeVar) (tus : List TypeUse) : StorageType :=
  match zt with
  | .val t => .val (substValType t tvs tus)
  | .pack pt => .pack pt

/-- `$subst_valtype` mapped over a `valtype*`. -/
def substValTypes (ts : ValTypes) (tvs : List TypeVar) (tus : List TypeUse) : ValTypes :=
  match ts with
  | .nil => .nil
  | .cons t rest => .cons (substValType t tvs tus) (substValTypes rest tvs tus)

/-- `def $subst_valtype`, all four equations. -/
def substValType (t : ValType) (tvs : List TypeVar) (tus : List TypeUse) : ValType :=
  match t with
  | .num nt => .num nt
  | .vec vt => .vec vt
  | .ref rt => .ref (substRefType rt tvs tus)
  | .bot => .bot

/-- `def $subst_reftype((REF null? ht), tv*, tu*) = REF null? $subst_heaptype(ht, tv*, tu*)`. -/
def substRefType (rt : RefType) (tvs : List TypeVar) (tus : List TypeUse) : RefType :=
  match rt with
  | .ref nul ht => .ref nul (substHeapType ht tvs tus)

/-- `def $subst_heaptype`, all three equations: a `typevar` is substituted, a
`deftype` is descended into, and any other heap type is unchanged. -/
def substHeapType (ht : HeapType) (tvs : List TypeVar) (tus : List TypeUse) : HeapType :=
  match ht with
  | .abs a => .abs a
  | .use tu => .use (substTypeUse tu tvs tus)

end

/-- `def $subst_tagtype(tu', tv*, tu*) = $subst_typeuse(tu', tv*, tu*)`. -/
def substTagType (jt : TagType) (tvs : List TypeVar) (tus : List TypeUse) : TagType :=
  substTypeUse jt tvs tus

/-- `def $subst_globaltype((mut? t), tv*, tu*) = mut? $subst_valtype(t, tv*, tu*)`. -/
def substGlobalType (gt : GlobalType) (tvs : List TypeVar) (tus : List TypeUse) : GlobalType :=
  { gt with valtype := substValType gt.valtype tvs tus }

/-- `def $subst_memtype((at lim PAGE), tv*, tu*) = at lim PAGE`. -/
def substMemType (mt : MemType) (_tvs : List TypeVar) (_tus : List TypeUse) : MemType := mt

/-- `def $subst_tabletype((at lim rt), tv*, tu*) = at lim $subst_reftype(rt, tv*, tu*)`. -/
def substTableType (tt : TableType) (tvs : List TypeVar) (tus : List TypeUse) : TableType :=
  { tt with elem := substRefType tt.elem tvs tus }

/-- `def $subst_externtype`, all five equations. -/
def substExternType (xt : ExternType) (tvs : List TypeVar) (tus : List TypeUse) : ExternType :=
  match xt with
  | .tag jt => .tag (substTagType jt tvs tus)
  | .global gt => .global (substGlobalType gt tvs tus)
  | .table tt => .table (substTableType tt tvs tus)
  | .mem mt => .mem (substMemType mt tvs tus)
  | .func tu => .func (substTypeUse tu tvs tus)

/-- `def $subst_moduletype(xt_1* -> xt_2*, tv*, tu*)`. -/
def substModuleType (mmt : ModuleType) (tvs : List TypeVar) (tus : List TypeUse) : ModuleType where
  imports := mmt.imports.map (substExternType · tvs tus)
  exports := mmt.exports.map (substExternType · tvs tus)

/-! ### Closing substitutions

`def $subst_all_X(x, tu^n) = $subst_X(x, (_IDX i)^(i<n), tu^n)`: replace every
type index below `n` by the corresponding entry of `tu^n`. -/

/-- `(_IDX i)^(i<n)`, the variable list every `$subst_all_*` uses. -/
def idxVars (n : Nat) : List TypeVar := (List.range n).map (fun i => TypeVar.idx (TypeIdx.ofNat i))

/-- `def $subst_all_valtype(t, tu^n) = $subst_valtype(t, (_IDX i)^(i<n), tu^n)`. -/
def substAllValType (t : ValType) (tus : List TypeUse) : ValType :=
  substValType t (idxVars tus.length) tus

/-- `def $subst_all_reftype(rt, tu^n)`. -/
def substAllRefType (rt : RefType) (tus : List TypeUse) : RefType :=
  substRefType rt (idxVars tus.length) tus

/-- `def $subst_all_deftype(dt, tu^n)`. -/
def substAllDefType (dt : DefType) (tus : List TypeUse) : DefType :=
  substDefType dt (idxVars tus.length) tus

/-- `def $subst_all_tagtype(jt, tu^n)`. -/
def substAllTagType (jt : TagType) (tus : List TypeUse) : TagType :=
  substTagType jt (idxVars tus.length) tus

/-- `def $subst_all_globaltype(gt, tu^n)`. -/
def substAllGlobalType (gt : GlobalType) (tus : List TypeUse) : GlobalType :=
  substGlobalType gt (idxVars tus.length) tus

/-- `def $subst_all_memtype(mt, tu^n)`. -/
def substAllMemType (mt : MemType) (tus : List TypeUse) : MemType :=
  substMemType mt (idxVars tus.length) tus

/-- `def $subst_all_tabletype(tt, tu^n)`. -/
def substAllTableType (tt : TableType) (tus : List TypeUse) : TableType :=
  substTableType tt (idxVars tus.length) tus

/-- `def $subst_all_externtype(xt, tu^n)`. -/
def substAllExternType (xt : ExternType) (tus : List TypeUse) : ExternType :=
  substExternType xt (idxVars tus.length) tus

/-- `def $subst_all_moduletype(mmt, tu^n)`. -/
def substAllModuleType (mmt : ModuleType) (tus : List TypeUse) : ModuleType :=
  substModuleType mmt (idxVars tus.length) tus

/-- `def $subst_all_deftypes(deftype*, typeuse*) : deftype*`. -/
def substAllDefTypes (dts : List DefType) (tus : List TypeUse) : List DefType :=
  dts.map (substAllDefType · tus)

/-! ## Rolling and unrolling -/

/-- `def $rollrt(x, rectype)
    = REC ($subst_subtype(subtype, ((_IDX $(x + i)))^(i<n), (REC i)^(i<n)))^n
    -- if rectype = REC subtype^n`.

Every self-reference of the group, written as the absolute type index `x + i`,
becomes the relative variable `REC i`. -/
def rollRt (x : TypeIdx) (qt : RecType) : RecType :=
  match qt with
  | .recr sts =>
      let n := SubTypes.length sts
      let tvs := (List.range n).map (fun i => TypeVar.idx (TypeIdx.ofNat (x.val + i)))
      let tus := (List.range n).map (fun i => TypeUse.recu i)
      .recr (substSubTypes sts tvs tus)

/-- `def $unrollrt(rectype)
    = REC ($subst_subtype(subtype, (REC i)^(i<n), (_DEF rectype i)^(i<n)))^n
    -- if rectype = REC subtype^n`.

Every relative variable `REC i` becomes the closed defined type `_DEF rectype i`. -/
def unrollRt (qt : RecType) : RecType :=
  match qt with
  | .recr sts =>
      let n := SubTypes.length sts
      let tvs := (List.range n).map (fun i => TypeVar.recv i)
      let tus := (List.range n).map (fun i => TypeUse.defd (.defd qt i))
      .recr (substSubTypes sts tvs tus)

/-- `def $rolldt(x, rectype) = (_DEF (REC subtype^n) i)^(i<n)
    -- if $rollrt(x, rectype) = REC subtype^n`. -/
def rollDt (x : TypeIdx) (qt : RecType) : List DefType :=
  match rollRt x qt with
  | .recr sts => (List.range (SubTypes.length sts)).map (fun i => DefType.defd (.recr sts) i)

/-- `def $unrolldt(_DEF rectype i) = subtype*[i] -- if $unrollrt(rectype) = REC subtype*`.

Partial: the source's equation applies only when `i` indexes the group. -/
def unrollDt : DefType → Option SubType
  | .defd qt i =>
      match unrollRt qt with
      | .recr sts => (SubTypes.toList sts)[i]?

/-- `def $expanddt(deftype) = comptype -- if $unrolldt(deftype) = SUB final? typeuse* comptype`. -/
def expandDt (dt : DefType) : Option CompType :=
  match unrollDt dt with
  | some (.sub _ _ ct) => some ct
  | none => none

/-- `def $as_deftype(typeuse) : deftype` with the single equation
`$as_deftype(dt) = dt`.  Partial: the source gives no equation at `_IDX` or
`REC`, so those are `none` here rather than a fabricated completion. -/
def asDefType : TypeUse → Option DefType
  | .defd dt => some dt
  | .idx _ => none
  | .recu _ => none

/-- `def $before(typeuse, typeidx, nat) : bool`, from
`2.1-validation.types.spectec`:

    $before(deftype, x, i) = true
    $before(_IDX typeidx, x, i) = typeidx < x
    $before(REC j, x, i) = j < i
-/
def before : TypeUse → TypeIdx → Nat → Bool
  | .defd _, _, _ => true
  | .idx y, x, _ => decide (y.val < x.val)
  | .recu j, _, i => decide (j < i)

/-- `def $is_packtype(storagetype) : bool` with `$is_packtype(zt) = zt = $unpack(zt)`,
from `2.3-validation.instructions.spectec`.

The equation is transcribed verbatim; note that it is TRUE exactly when `zt` is
*not* a packed type (`$unpack(I8) = I32 =/= I8`, while `$unpack(I32) = I32`), so
the source's name and its `hint(prose)` are the wrong way round.  The two uses
of it, `Instr_ok/struct.get` and `Instr_ok/array.get`, read
`sx? = eps <=> $is_packtype(zt)` -- no sign extension exactly when the field is
unpacked -- which is what the equation, not the name, says.  The Lean name
follows the equation. -/
def StorageType.isUnpacked (zt : StorageType) : Bool :=
  decide (zt = StorageType.val (StorageType.unpack zt))

/-! ## Sequence functions used by the typing rules

`0.3-aux.seq.spectec`. -/

/-- `def $setminus1_(syntax X, X, X*) : X*`. -/
def setminus1 {X : Type} [DecidableEq X] (w : X) : List X → List X
  | [] => [w]
  | w₁ :: ws => if w = w₁ then [] else setminus1 w ws

/-- `def $setminus_(syntax X, X*, X*) : X*`. -/
def setminus {X : Type} [DecidableEq X] : List X → List X → List X
  | [], _ => []
  | w₁ :: ws, vs => setminus1 w₁ vs ++ setminus ws vs

/-- `def $disjoint_(syntax X, X*) : bool`: no element repeats. -/
def disjoint {X : Type} [DecidableEq X] : List X → Bool
  | [] => true
  | w :: ws => !(ws.contains w) && disjoint ws

end WasmGemmGnaf.Wasm.Core
