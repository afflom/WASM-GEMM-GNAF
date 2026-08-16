import WasmGemmGnaf.Wasm.Core.TypeGraphClosure
import WasmGemmGnaf.Wasm.Core.ValidateStoredCompOk

set_option autoImplicit false
set_option maxRecDepth 16000

namespace WasmGemmGnaf.Wasm.Core

/-! ## Causal closure stability under a final-vector extension -/

private theorem closDefTypesAux_append_finalStored
    (acc left right : List DefType) :
    closDefTypesAux acc (left ++ right) =
      closDefTypesAux (closDefTypesAux acc left) right := by
  induction left generalizing acc with
  | nil => rfl
  | cons dt rest ih =>
      simp only [List.cons_append, closDefTypesAux]
      exact ih _

theorem closDefTypes_append_finalStored (pre tail : List DefType) :
    closDefTypes (pre ++ tail) =
      closDefTypesAux (closDefTypes pre) tail := by
  unfold closDefTypes
  exact closDefTypesAux_append_finalStored [] pre tail

theorem closDefTypes_prefix_finalStored (pre tail : List DefType) :
    ∃ suffix, closDefTypes (pre ++ tail) = closDefTypes pre ++ suffix := by
  rw [closDefTypes_append_finalStored]
  exact closDefTypesAux_prefix (closDefTypes pre) tail

/-- Closing a type whose free indices lie in a prefix is unchanged when the
final checked type vector appends a suffix.  This is the exact closure-equality
premise needed by the `Deftype_subA.refl` arm of reroll preservation. -/
theorem Context.closDefType_eq_of_types_prefix
    {pre tail : List DefType} (hbound : pre.length + tail.length ≤ 2 ^ 32)
    {dt : DefType} (hfree : TypesBelow pre.length (freeDefType dt)) :
    ({ Context.empty with types := pre } : Context).closDefType dt =
      ({ Context.empty with types := pre ++ tail } : Context).closDefType dt := by
  obtain ⟨suffix, hsuffix⟩ := closDefTypes_prefix_finalStored pre tail
  have hpreLen : (closDefTypes pre).length = pre.length := by
    simpa [closDefTypes] using closDefTypesAux_length [] pre
  have hfullLen : (closDefTypes (pre ++ tail)).length =
      pre.length + tail.length := by
    simpa [closDefTypes, List.length_append] using
      closDefTypesAux_length [] (pre ++ tail)
  have hsuffixLen : suffix.length = tail.length := by
    have hlen := congrArg List.length hsuffix
    simp only [List.length_append, hpreLen, hfullLen] at hlen
    omega
  have hagree : ClosingEnvsAgree (freeDefType dt)
      ((closDefTypes pre).map TypeUse.defd)
      ((closDefTypes (pre ++ tail)).map TypeUse.defd) := by
    intro x hx
    have hxlt : x.val < pre.length := hfree x hx
    rw [hsuffix, List.map_append]
    exact substTypeVar_idxVars_prefix
      (pre := (closDefTypes pre).map TypeUse.defd)
      (suffix := suffix.map TypeUse.defd)
      (x := x)
      (by simpa [hpreLen, hsuffixLen] using hbound)
      (by simpa [hpreLen] using hxlt)
  simpa [Context.closDefType, Context.closTypes] using
    subst_defType_env dt
      ((closDefTypes pre).map TypeUse.defd)
      ((closDefTypes (pre ++ tail)).map TypeUse.defd) hagree

/-!
# Semantic validity of the final stored type vector

The type-section judgment validates source composites before `$rollrt` turns
the current group's absolute indices into relative `REC` variables.  The
lemmas in this section isolate the structural validity half of that transport:
rolling a syntactic composite preserves validity whenever the target context
extends the source type vector and has enough recursive scratch entries.
-/

theorem rollHeaptypeOkA
    {E R : Context} {base : TypeIdx} {n : Nat} {ht : HeapType}
    (htypes : ∃ tail, R.types = E.types ++ tail)
    (hrecs : n ≤ R.recs.length) (hbound : base.val + n ≤ 2 ^ 32)
    (hsyn : ht.isSyn = true) (h : Heaptype_okA E ht) :
    Heaptype_okA R
      (substHeapType ht (rollTVars base n) (rollTUses n)) := by
  cases ht with
  | abs a => exact .abs
  | use tu =>
      cases tu with
      | recu i => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | defd dt => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | idx y =>
          cases h with
          | typeuse htu =>
              cases htu with
              | typeidx hlookup =>
                  rename_i dt
                  simp only [substHeapType, substTypeUse, rollTVars, rollTUses]
                  rw [substTypeVar_rollVars base y n hbound]
                  split
                  · rename_i hrange
                    have hj : y.val - base.val < R.recs.length := by omega
                    let st := R.recs[y.val - base.val]'hj
                    exact .typeuse (.rec_ (st := st)
                      (List.getElem?_eq_getElem hj))
                  ·
                    obtain ⟨tail, htypes⟩ := htypes
                    have hy : y.val < E.types.length :=
                      (List.getElem?_eq_some_iff.mp hlookup).1
                    have hlookupR : R.types[y.val]? = some dt := by
                      rw [htypes, List.getElem?_append_left hy]
                      exact hlookup
                    exact .typeuse (.typeidx hlookupR)

theorem rollReftypeOkA
    {E R : Context} {base : TypeIdx} {n : Nat} {rt : RefType}
    (htypes : ∃ tail, R.types = E.types ++ tail)
    (hrecs : n ≤ R.recs.length) (hbound : base.val + n ≤ 2 ^ 32)
    (hsyn : rt.isSyn = true) (h : Reftype_okA E rt) :
    Reftype_okA R (substRefType rt (rollTVars base n) (rollTUses n)) := by
  cases rt with
  | ref nul ht =>
      cases h with
      | mk hht =>
          exact .mk (rollHeaptypeOkA htypes hrecs hbound hsyn hht)

theorem rollValtypeOkA
    {E R : Context} {base : TypeIdx} {n : Nat} {t : ValType}
    (htypes : ∃ tail, R.types = E.types ++ tail)
    (hrecs : n ≤ R.recs.length) (hbound : base.val + n ≤ 2 ^ 32)
    (hsyn : t.isSyn = true) (h : Valtype_okA E t) :
    Valtype_okA R (substValType t (rollTVars base n) (rollTUses n)) := by
  cases t with
  | num nt => exact .num .mk
  | vec vt => exact .vec .mk
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt =>
      cases h with
      | ref hrt =>
          exact .ref (rollReftypeOkA htypes hrecs hbound hsyn hrt)

theorem rollStoragetypeOkA
    {E R : Context} {base : TypeIdx} {n : Nat} {zt : StorageType}
    (htypes : ∃ tail, R.types = E.types ++ tail)
    (hrecs : n ≤ R.recs.length) (hbound : base.val + n ≤ 2 ^ 32)
    (hsyn : zt.isSyn = true) (h : Storagetype_okA E zt) :
    Storagetype_okA R
      (substStorageType zt (rollTVars base n) (rollTUses n)) := by
  cases zt with
  | pack pt => exact .pack .mk
  | val t =>
      cases h with
      | val ht => exact .val (rollValtypeOkA htypes hrecs hbound hsyn ht)

theorem rollFieldtypeOkA
    {E R : Context} {base : TypeIdx} {n : Nat} {ft : FieldType}
    (htypes : ∃ tail, R.types = E.types ++ tail)
    (hrecs : n ≤ R.recs.length) (hbound : base.val + n ≤ 2 ^ 32)
    (hsyn : ft.isSyn = true) (h : Fieldtype_okA E ft) :
    Fieldtype_okA R
      (substFieldType ft (rollTVars base n) (rollTUses n)) := by
  cases ft with
  | mk m zt =>
      cases h with
      | mk hzt =>
          exact .mk (rollStoragetypeOkA htypes hrecs hbound hsyn hzt)

private theorem fieldTypes_substRoll : ∀ (fts : FieldTypes)
    {E R : Context} {base : TypeIdx} {n : Nat},
    (∃ tail, R.types = E.types ++ tail) →
    n ≤ R.recs.length → base.val + n ≤ 2 ^ 32 →
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    SeqAll (Fieldtype_okA E) (FieldTypes.toList fts) →
    SeqAll (Fieldtype_okA R)
      (FieldTypes.toList
        (substFieldTypes fts (rollTVars base n) (rollTUses n))) := by
  intro fts
  cases fts with
  | nil =>
      intro E R base n htypes hrecs hbound hsyn hall candidate hcandidate
      simp [substFieldTypes, FieldTypes.toList] at hcandidate
  | cons ft fts =>
      intro E R base n htypes hrecs hbound hsyn hall
      simp only [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substFieldTypes, FieldTypes.toList]
      intro candidate hcandidate
      rw [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | hcandidate
      · exact rollFieldtypeOkA htypes hrecs hbound hsyn.1
          (hall ft (by simp [FieldTypes.toList]))
      · exact fieldTypes_substRoll fts htypes hrecs hbound hsyn.2
          (fun field hfield => hall field (by
            simp [FieldTypes.toList, hfield])) candidate hcandidate

private theorem valTypes_substRoll : ∀ (ts : ValTypes)
    {E R : Context} {base : TypeIdx} {n : Nat},
    (∃ tail, R.types = E.types ++ tail) →
    n ≤ R.recs.length → base.val + n ≤ 2 ^ 32 →
    (ValTypes.toList ts).all ValType.isSyn = true →
    SeqAll (Valtype_okA E) (ValTypes.toList ts) →
    SeqAll (Valtype_okA R)
      (ValTypes.toList
        (substValTypes ts (rollTVars base n) (rollTUses n))) := by
  intro ts
  cases ts with
  | nil =>
      intro E R base n htypes hrecs hbound hsyn hall candidate hcandidate
      simp [substValTypes, ValTypes.toList] at hcandidate
  | cons t ts =>
      intro E R base n htypes hrecs hbound hsyn hall
      simp only [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substValTypes, ValTypes.toList]
      intro candidate hcandidate
      rw [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | hcandidate
      · exact rollValtypeOkA htypes hrecs hbound hsyn.1
          (hall t (by simp [ValTypes.toList]))
      · exact valTypes_substRoll ts htypes hrecs hbound hsyn.2
          (fun value hvalue => hall value (by
            simp [ValTypes.toList, hvalue])) candidate hcandidate

theorem rollComptypeOkA
    {E R : Context} {base : TypeIdx} {n : Nat} {ct : CompType}
    (htypes : ∃ tail, R.types = E.types ++ tail)
    (hrecs : n ≤ R.recs.length) (hbound : base.val + n ≤ 2 ^ 32)
    (hsyn : ct.isSyn = true) (h : Comptype_okA E ct) :
    Comptype_okA R
      (substCompType ct (rollTVars base n) (rollTUses n)) := by
  cases ct with
  | struct fts =>
      cases h with
      | struct hall =>
          exact .struct (fieldTypes_substRoll fts htypes hrecs hbound hsyn hall)
  | array ft =>
      cases h with
      | array hft =>
          exact .array (rollFieldtypeOkA htypes hrecs hbound hsyn hft)
  | func dom cod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      cases h with
      | func hdom hcod =>
          cases hdom with
          | mk hdom =>
              cases hcod with
              | mk hcod =>
                  exact .func
                    (.mk (valTypes_substRoll dom htypes hrecs hbound
                      hsyn.1 hdom))
                    (.mk (valTypes_substRoll cod htypes hrecs hbound
                      hsyn.2 hcod))

/-! ## Structural lift of a heap-level roll theorem -/

private theorem seqAll₂_map
    {A B A' B' : Type} {P : A → B → Prop}
    {Q : A' → B' → Prop} {as : List A} {bs : List B}
    {f : A → A'} {g : B → B'}
    (_hlen : SeqLen₂ as bs) (hall : SeqAll₂ P as bs)
    (hmap : ∀ {a b}, P a b → Q (f a) (g b)) :
    SeqAll₂ Q (as.map f) (bs.map g) := by
  intro i a' b' ha' hb'
  rw [List.getElem?_map] at ha' hb'
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp ha'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
  exact hmap (hall i a b ha hb)

theorem rollReftypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {left right : RefType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R
        (substHeapType h₁ (rollTVars base n) (rollTUses n))
        (substHeapType h₂ (rollTVars base n) (rollTUses n)))
    (h : Reftype_subA E left right) :
    Reftype_subA R
      (substRefType left (rollTVars base n) (rollTUses n))
      (substRefType right (rollTVars base n) (rollTUses n)) := by
  cases h with
  | nonnull hs => exact .nonnull (hheap hs)
  | null hs => exact .null (hheap hs)

theorem rollValtypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {left right : ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R
        (substHeapType h₁ (rollTVars base n) (rollTUses n))
        (substHeapType h₂ (rollTVars base n) (rollTUses n)))
    (h : Valtype_subA E left right) :
    Valtype_subA R
      (substValType left (rollTVars base n) (rollTUses n))
      (substValType right (rollTVars base n) (rollTUses n)) := by
  cases h with
  | num hs => cases hs; exact .num .mk
  | vec hs => cases hs; exact .vec .mk
  | ref hs => exact .ref (rollReftypeSubA hheap hs)
  | bot => exact .bot

theorem rollStoragetypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat}
    {left right : StorageType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R
        (substHeapType h₁ (rollTVars base n) (rollTUses n))
        (substHeapType h₂ (rollTVars base n) (rollTUses n)))
    (h : Storagetype_subA E left right) :
    Storagetype_subA R
      (substStorageType left (rollTVars base n) (rollTUses n))
      (substStorageType right (rollTVars base n) (rollTUses n)) := by
  cases h with
  | val hs => exact .val (rollValtypeSubA hheap hs)
  | pack hs => cases hs; exact .pack .mk

theorem rollFieldtypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat}
    {left right : FieldType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R
        (substHeapType h₁ (rollTVars base n) (rollTUses n))
        (substHeapType h₂ (rollTVars base n) (rollTUses n)))
    (h : Fieldtype_subA E left right) :
    Fieldtype_subA R
      (substFieldType left (rollTVars base n) (rollTUses n))
      (substFieldType right (rollTVars base n) (rollTUses n)) := by
  cases h with
  | const hs => exact .const (rollStoragetypeSubA hheap hs)
  | var hs₁ hs₂ =>
      simpa [substFieldType] using Fieldtype_subA.var
        (rollStoragetypeSubA hheap hs₁)
        (rollStoragetypeSubA hheap hs₂)

private theorem resulttypeSubA_map
    {E R : Context} {base : TypeIdx} {n : Nat}
    {left right : List ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R
        (substHeapType h₁ (rollTVars base n) (rollTUses n))
        (substHeapType h₂ (rollTVars base n) (rollTUses n)))
    (h : Resulttype_subA E left right) :
    Resulttype_subA R
      (left.map (fun t => substValType t (rollTVars base n) (rollTUses n)))
      (right.map (fun t => substValType t (rollTVars base n) (rollTUses n))) := by
  cases h with
  | mk hlen hall =>
      exact .mk (by simpa [SeqLen₂] using hlen)
        (seqAll₂_map hlen hall (rollValtypeSubA hheap))

private theorem FieldTypes.toList_substRoll
    (fts : FieldTypes) (base : TypeIdx) (n : Nat) :
    FieldTypes.toList
        (substFieldTypes fts (rollTVars base n) (rollTUses n)) =
      (FieldTypes.toList fts).map
        (fun ft => substFieldType ft (rollTVars base n) (rollTUses n)) := by
  cases fts with
  | nil => rfl
  | cons ft rest =>
      simp only [substFieldTypes, FieldTypes.toList, List.map_cons]
      exact congrArg (List.cons _) (FieldTypes.toList_substRoll rest base n)

private theorem FieldTypes.substRoll_ofList
    (fts : List FieldType) (base : TypeIdx) (n : Nat) :
    substFieldTypes (FieldTypes.ofList fts) (rollTVars base n) (rollTUses n) =
      FieldTypes.ofList (fts.map
        (fun ft => substFieldType ft (rollTVars base n) (rollTUses n))) := by
  induction fts with
  | nil => rfl
  | cons ft rest ih =>
      simp only [FieldTypes.ofList, substFieldTypes, List.map_cons]
      rw [ih]

private theorem ValTypes.toList_substRoll
    (ts : ValTypes) (base : TypeIdx) (n : Nat) :
    ValTypes.toList (substValTypes ts (rollTVars base n) (rollTUses n)) =
      (ValTypes.toList ts).map
        (fun t => substValType t (rollTVars base n) (rollTUses n)) := by
  cases ts with
  | nil => rfl
  | cons t rest =>
      simp only [substValTypes, ValTypes.toList, List.map_cons]
      exact congrArg (List.cons _) (ValTypes.toList_substRoll rest base n)

theorem rollComptypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat}
    {left right : CompType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R
        (substHeapType h₁ (rollTVars base n) (rollTUses n))
        (substHeapType h₂ (rollTVars base n) (rollTUses n)))
    (h : Comptype_subA E left right) :
    Comptype_subA R
      (substCompType left (rollTVars base n) (rollTUses n))
      (substCompType right (rollTVars base n) (rollTUses n)) := by
  cases h with
  | @struct _ fts₁ extra fts₂ hlen hall =>
      have hfields := seqAll₂_map hlen hall (rollFieldtypeSubA hheap)
      simp only [substCompType, FieldTypes.substRoll_ofList, List.map_append]
      apply Comptype_subA.struct
        (fts₁ := fts₁.map
          (fun ft => substFieldType ft (rollTVars base n) (rollTUses n)))
        (fts₁' := extra.map
          (fun ft => substFieldType ft (rollTVars base n) (rollTUses n)))
        (fts₂ := fts₂.map
          (fun ft => substFieldType ft (rollTVars base n) (rollTUses n)))
      · simpa [SeqLen₂] using hlen
      · exact hfields
  | array hs => exact .array (rollFieldtypeSubA hheap hs)
  | @func _ dom₁ cod₁ dom₂ cod₂ hdom hcod =>
      apply Comptype_subA.func
      · rw [ValTypes.toList_substRoll, ValTypes.toList_substRoll]
        exact resulttypeSubA_map hheap hdom
      · rw [ValTypes.toList_substRoll, ValTypes.toList_substRoll]
        exact resulttypeSubA_map hheap hcod

/-! ## Canonical rerolling of unrolled current-group aliases -/

/-- Replace both presentations of a current-group member--its source index
and the `_DEF` produced by unrolling the rolled group--with the corresponding
`REC`.  Other semantic defined types are deliberately left opaque. -/
def rerollTypeUse (base : TypeIdx) (n : Nat) (rolled : RecType) :
    TypeUse → TypeUse
  | .idx x =>
      if base.val ≤ x.val ∧ x.val < base.val + n then
        .recu (x.val - base.val)
      else .idx x
  | .recu i => .recu i
  | .defd (.defd qt i) =>
      if qt = rolled then .recu i else .defd (.defd qt i)

def rerollHeapType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    HeapType → HeapType
  | .abs a => .abs a
  | .use tu => .use (rerollTypeUse base n rolled tu)

def rerollRefType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    RefType → RefType
  | .ref nul ht => .ref nul (rerollHeapType base n rolled ht)

def rerollValType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    ValType → ValType
  | .num nt => .num nt
  | .vec vt => .vec vt
  | .ref rt => .ref (rerollRefType base n rolled rt)
  | .bot => .bot

def rerollStorageType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    StorageType → StorageType
  | .pack pt => .pack pt
  | .val t => .val (rerollValType base n rolled t)

def rerollFieldType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    FieldType → FieldType
  | .mk mutability storage =>
      .mk mutability (rerollStorageType base n rolled storage)

def rerollFieldTypes (base : TypeIdx) (n : Nat) (rolled : RecType) :
    FieldTypes → FieldTypes
  | .nil => .nil
  | .cons field rest => .cons (rerollFieldType base n rolled field)
      (rerollFieldTypes base n rolled rest)

def rerollValTypes (base : TypeIdx) (n : Nat) (rolled : RecType) :
    ValTypes → ValTypes
  | .nil => .nil
  | .cons t rest => .cons (rerollValType base n rolled t)
      (rerollValTypes base n rolled rest)

def rerollCompType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    CompType → CompType
  | .struct fields => .struct (rerollFieldTypes base n rolled fields)
  | .array field => .array (rerollFieldType base n rolled field)
  | .func dom cod => .func (rerollValTypes base n rolled dom)
      (rerollValTypes base n rolled cod)

def rerollTypeUses (base : TypeIdx) (n : Nat) (rolled : RecType) :
    TypeUses → TypeUses
  | .nil => .nil
  | .cons tu rest => .cons (rerollTypeUse base n rolled tu)
      (rerollTypeUses base n rolled rest)

def rerollSubType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    SubType → SubType
  | .sub fin sups ct => .sub fin (rerollTypeUses base n rolled sups)
      (rerollCompType base n rolled ct)

def rerollSubTypes (base : TypeIdx) (n : Nat) (rolled : RecType) :
    SubTypes → SubTypes
  | .nil => .nil
  | .cons st rest => .cons (rerollSubType base n rolled st)
      (rerollSubTypes base n rolled rest)

def rerollRecType (base : TypeIdx) (n : Nat) (rolled : RecType) :
    RecType → RecType
  | .recr sts => .recr (rerollSubTypes base n rolled sts)

/-!
## Proof-indexed origins for current-group aliases

`rerollTypeUse` is intentionally only a convenient term operation: structural
equality cannot distinguish a literal introduced by unrolling the current
group from an equal literal already stored in an earlier group.  The relation
below retains the lookup index that introduced such a literal.  In particular,
`defd_keep` and `defd_at` may both describe the same source term, but only the
latter carries authority to replace that occurrence by the corresponding
`REC`.  Subsequent semantic transport must consume this proof, rather than
case-splitting on `DefType` equality.
-/

inductive TypeUse.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    TypeUse → TypeUse → Prop where
  | idx_in {x : TypeIdx} (hlo : base.val ≤ x.val)
      (hhi : x.val < base.val + n) :
      RerollOriginA E base n (.idx x) (.recu (x.val - base.val))
  | idx_out {x : TypeIdx} (hout : ¬ (base.val ≤ x.val ∧
      x.val < base.val + n)) :
      RerollOriginA E base n (.idx x) (.idx x)
  | recu (i : Nat) : RerollOriginA E base n (.recu i) (.recu i)
  | defd_keep (dt : DefType) :
      RerollOriginA E base n (.defd dt) (.defd dt)
  | defd_at {i : Nat} {dt : DefType} (hi : i < n)
      (hlookup : E.types[base.val + i]? = some dt) :
      RerollOriginA E base n (.defd dt) (.recu i)

inductive HeapType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    HeapType → HeapType → Prop where
  | abs (a : AbsHeapType) : RerollOriginA E base n (.abs a) (.abs a)
  | use {source target : TypeUse} :
      TypeUse.RerollOriginA E base n source target →
      RerollOriginA E base n (.use source) (.use target)

inductive RefType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    RefType → RefType → Prop where
  | ref {nul : Option Null} {source target : HeapType} :
      HeapType.RerollOriginA E base n source target →
      RerollOriginA E base n (.ref nul source) (.ref nul target)

inductive ValType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    ValType → ValType → Prop where
  | num (nt : NumType) : RerollOriginA E base n (.num nt) (.num nt)
  | vec (vt : VecType) : RerollOriginA E base n (.vec vt) (.vec vt)
  | ref {source target : RefType} :
      RefType.RerollOriginA E base n source target →
      RerollOriginA E base n (.ref source) (.ref target)
  | bot : RerollOriginA E base n .bot .bot

inductive StorageType.RerollOriginA
    (E : Context) (base : TypeIdx) (n : Nat) :
    StorageType → StorageType → Prop where
  | pack (pt : PackType) : RerollOriginA E base n (.pack pt) (.pack pt)
  | val {source target : ValType} :
      ValType.RerollOriginA E base n source target →
      RerollOriginA E base n (.val source) (.val target)

inductive FieldType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    FieldType → FieldType → Prop where
  | mk {mutability : Option Mut} {source target : StorageType} :
      StorageType.RerollOriginA E base n source target →
      RerollOriginA E base n (.mk mutability source) (.mk mutability target)

inductive FieldTypes.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    FieldTypes → FieldTypes → Prop where
  | nil : RerollOriginA E base n .nil .nil
  | cons {sourceHead targetHead : FieldType}
      {sourceTail targetTail : FieldTypes} :
      FieldType.RerollOriginA E base n sourceHead targetHead →
      RerollOriginA E base n sourceTail targetTail →
      RerollOriginA E base n (.cons sourceHead sourceTail)
        (.cons targetHead targetTail)

inductive ValTypes.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    ValTypes → ValTypes → Prop where
  | nil : RerollOriginA E base n .nil .nil
  | cons {sourceHead targetHead : ValType}
      {sourceTail targetTail : ValTypes} :
      ValType.RerollOriginA E base n sourceHead targetHead →
      RerollOriginA E base n sourceTail targetTail →
      RerollOriginA E base n (.cons sourceHead sourceTail)
        (.cons targetHead targetTail)

inductive CompType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    CompType → CompType → Prop where
  | struct {source target : FieldTypes} :
      FieldTypes.RerollOriginA E base n source target →
      RerollOriginA E base n (.struct source) (.struct target)
  | array {source target : FieldType} :
      FieldType.RerollOriginA E base n source target →
      RerollOriginA E base n (.array source) (.array target)
  | func {sourceDom targetDom sourceCod targetCod : ValTypes} :
      ValTypes.RerollOriginA E base n sourceDom targetDom →
      ValTypes.RerollOriginA E base n sourceCod targetCod →
      RerollOriginA E base n (.func sourceDom sourceCod)
        (.func targetDom targetCod)

inductive TypeUses.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    TypeUses → TypeUses → Prop where
  | nil : RerollOriginA E base n .nil .nil
  | cons {sourceHead targetHead : TypeUse}
      {sourceTail targetTail : TypeUses} :
      TypeUse.RerollOriginA E base n sourceHead targetHead →
      RerollOriginA E base n sourceTail targetTail →
      RerollOriginA E base n (.cons sourceHead sourceTail)
        (.cons targetHead targetTail)

inductive SubType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    SubType → SubType → Prop where
  | sub {fin : Option Final} {sourceSups targetSups : TypeUses}
      {sourceComp targetComp : CompType} :
      TypeUses.RerollOriginA E base n sourceSups targetSups →
      CompType.RerollOriginA E base n sourceComp targetComp →
      RerollOriginA E base n (.sub fin sourceSups sourceComp)
        (.sub fin targetSups targetComp)

inductive SubTypes.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    SubTypes → SubTypes → Prop where
  | nil : RerollOriginA E base n .nil .nil
  | cons {sourceHead targetHead : SubType}
      {sourceTail targetTail : SubTypes} :
      SubType.RerollOriginA E base n sourceHead targetHead →
      RerollOriginA E base n sourceTail targetTail →
      RerollOriginA E base n (.cons sourceHead sourceTail)
        (.cons targetHead targetTail)

inductive RecType.RerollOriginA (E : Context) (base : TypeIdx) (n : Nat) :
    RecType → RecType → Prop where
  | recr {source target : SubTypes} :
      SubTypes.RerollOriginA E base n source target →
      RerollOriginA E base n (.recr source) (.recr target)

/-- A ranked source node with an unambiguous prefix/current-group origin.
Unlike a bare `defd` term, the even source rank retains the vector index that
introduced it, so structurally equal members at different indices cannot be
silently rerolled as one another. -/
inductive TypeUse.RankedRerollOriginA
    (E : Context) (base : TypeIdx) (n : Nat) :
    TypeUse → TypeUse → Nat → Prop where
  | idx_prefix {x : TypeIdx} {dt : DefType}
      (hprefix : x.val < base.val)
      (hlookup : E.types[x.val]? = some dt) :
      RankedRerollOriginA E base n (.idx x) (.idx x) (2 * x.val + 1)
  | idx_current {x : TypeIdx} {dt : DefType}
      (hlo : base.val ≤ x.val) (hhi : x.val < base.val + n)
      (hlookup : E.types[x.val]? = some dt) :
      RankedRerollOriginA E base n (.idx x)
        (.recu (x.val - base.val)) (2 * x.val + 1)
  | defd_prefix {i : Nat} {dt : DefType}
      (hprefix : i < base.val) (hlookup : E.types[i]? = some dt) :
      RankedRerollOriginA E base n (.defd dt) (.defd dt) (2 * i)
  | defd_current {i : Nat} {dt : DefType}
      (hi : i < n) (hlookup : E.types[base.val + i]? = some dt) :
      RankedRerollOriginA E base n (.defd dt) (.recu i)
        (2 * (base.val + i))

/-- Provenance for a declared supertype of current group member `i`.
The source occurrence is either an index into the already checked prefix or
the literal produced by unrolling an earlier member of the same group.  This
is deliberately relational: equal `DefType` values at different vector
positions retain their distinct introduction indices. -/
inductive TypeUse.RerollBeforeA
    (E : Context) (base : TypeIdx) (n i : Nat) :
    TypeUse → TypeUse → Prop where
  | idx_prefix {x : TypeIdx} {dt : DefType}
      (hprefix : x.val < base.val)
      (hlookup : E.types[x.val]? = some dt) :
      RerollBeforeA E base n i (.idx x) (.idx x)
  | defd_current {j : Nat} {dt : DefType}
      (hbefore : j < i) (hgroup : j < n)
      (hlookup : E.types[base.val + j]? = some dt) :
      RerollBeforeA E base n i (.defd dt) (.recu j)

theorem TypeUse.RerollBeforeA.origin
    {E : Context} {base : TypeIdx} {n i : Nat}
    {source target : TypeUse}
    (h : TypeUse.RerollBeforeA E base n i source target) :
    TypeUse.RerollOriginA E base n source target := by
  cases h with
  | idx_prefix hprefix _ =>
      exact .idx_out (fun hrange => by omega)
  | defd_current _ hgroup hlookup =>
      exact .defd_at hgroup hlookup

theorem TypeUse.RerollBeforeA.ranked
    {E : Context} {base : TypeIdx} {n i : Nat}
    {source target : TypeUse}
    (h : TypeUse.RerollBeforeA E base n i source target) :
    ∃ r : Nat, r < 2 * (base.val + i) ∧
      TypeUse.RankedRerollOriginA E base n source target r := by
  cases h with
  | idx_prefix hprefix hlookup =>
      exact ⟨2 * _ + 1, by omega, .idx_prefix hprefix hlookup⟩
  | defd_current hbefore hgroup hlookup =>
      exact ⟨2 * (base.val + _) , by omega,
        .defd_current hgroup hlookup⟩

theorem TypeUse.RerollBeforeA.before
    {E : Context} {base : TypeIdx} {n i : Nat}
    {source target : TypeUse}
    (hbound : base.val + n ≤ 2 ^ 32) (hi : i < n)
    (h : TypeUse.RerollBeforeA E base n i source target) :
    before target (TypeIdx.ofNat (base.val + i)) i = true := by
  cases h with
  | idx_prefix hprefix _ =>
      change decide (_ < (TypeIdx.ofNat (base.val + i)).val) = true
      rw [decide_eq_true_eq]
      rw [TypeIdx.ofNat_val_of_lt]
      · omega
      · omega
  | defd_current hbefore _ _ =>
      change decide (_ < i) = true
      simpa only [decide_eq_true_eq] using hbefore

/-! The declaration-site ordering fact retained by the grammar judgments. -/

private theorem comptypeSubA_absShape_eq_finalStored
    {C : Context} {left right : CompType}
    (h : Comptype_subA C left right) : left.absShape = right.absShape := by
  cases h <;> rfl

private def RawSourceSupersBeforeA (C : Context) (limit : Nat) :
    SubType → Prop
  | .sub _ sups ct =>
      ∀ tu ∈ TypeUses.toList sups,
        ∃ (y : TypeIdx) (dt : DefType),
          tu = .idx y ∧ y.val < limit ∧ C.types[y.val]? = some dt ∧
            dt.absShape = some ct.absShape

private theorem Subtype_okA.rawSourceSupersBeforeA
    {C : Context} {st : SubType} {x : TypeIdx}
    (h : Subtype_okA C st x) : RawSourceSupersBeforeA C x.val st := by
  cases h with
  | @mk C' fin xs ct x' cts' hlen hlen₂ hall hok hsub =>
      intro tu htu
      simp only [TypeUses.toList_ofList] at htu
      obtain ⟨y, hyxs, rfl⟩ := List.mem_map.mp htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hyxs
      have hjlt : j < xs.length := (List.getElem?_eq_some_iff.mp hj).1
      have hjctlt : j < cts'.length := by
        simpa [SeqLen₂] using (hlen₂ ▸ hjlt)
      let ct' := cts'[j]
      have hp := hall j y ct' hj (List.getElem?_eq_getElem hjctlt)
      obtain ⟨hy, dt, _, _, hlookup, hunroll⟩ := hp
      have hctsub : Comptype_subA C ct ct' :=
        hsub ct' (List.mem_of_getElem? (List.getElem?_eq_getElem hjctlt))
      have hshape : dt.absShape = some ct.absShape := by
        rw [DefType.absShape, expandDt, hunroll]
        simp [comptypeSubA_absShape_eq_finalStored hctsub]
      exact ⟨y, dt, rfl, hy, hlookup, hshape⟩

private theorem Subtype_ok2A.rawSourceSupersBeforeA
    {C : Context} {st : SubType} {x : TypeIdx} {i : Nat}
    (hsyn : st.isSyn = true) (h : Subtype_ok2A C st x i) :
    RawSourceSupersBeforeA C x.val st := by
  cases h with
  | @mk C' fin sups ct x' i' cts' hlen hlen₂ hall hvalid hok hsub =>
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      intro tu htu
      have htuSyn : tu.isSyn = true :=
        List.all_eq_true.mp hsyn.1 tu htu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp htu
      have hjlt : j < (TypeUses.toList sups).length :=
        (List.getElem?_eq_some_iff.mp hj).1
      have hjctlt : j < cts'.length := by
        simpa [SeqLen₂] using (hlen₂ ▸ hjlt)
      let ct' := cts'[j]
      have hp := hall j tu ct' hj (List.getElem?_eq_getElem hjctlt)
      obtain ⟨hbef, fin', sups', hunrollHt⟩ := hp
      have hok := hvalid tu htu
      have hctsub : Comptype_subA C ct ct' :=
        hsub ct' (List.mem_of_getElem? (List.getElem?_eq_getElem hjctlt))
      cases tu with
      | defd _ | recu _ => simp [TypeUse.isSyn] at htuSyn
      | idx y =>
          cases hok with
          | typeidx hlookup =>
              let dt := C.types[y.val]'(List.getElem?_eq_some_iff.mp hlookup).1
              have hdt : C.types[y.val]? = some dt :=
                List.getElem?_eq_getElem _
              have hunroll : unrollDt dt = some (.sub fin' sups' ct') := by
                simpa [Context.unrollHt, hdt] using hunrollHt
              have hshape : dt.absShape = some ct.absShape := by
                rw [DefType.absShape, expandDt, hunroll]
                simp [comptypeSubA_absShape_eq_finalStored hctsub]
              exact ⟨y, dt, rfl, by simpa [before] using hbef,
                hdt, hshape⟩

private theorem Rectype_ok2A.rawSourceSupersBeforeAt
    {C : Context} {sts : SubTypes} {x : TypeIdx} {i : Nat}
    (hrange : x.val + SubTypes.length sts ≤ 2 ^ 32)
    (hsyn : (RecType.recr sts).isSyn = true)
    (h : Rectype_ok2A C (.recr sts) x i) :
    ∀ {k : Nat} {st : SubType},
      (SubTypes.toList sts)[k]? = some st →
      RawSourceSupersBeforeA C (x.val + k) st := by
  cases h with
  | empty =>
      intro k st hget
      simp [SubTypes.toList] at hget
  | @cons C' head tail x i hst htail =>
      rw [RecType.isSyn, SubTypes.toList, List.all_cons,
        Bool.and_eq_true] at hsyn
      intro k candidate hget
      cases k with
      | zero =>
          simp only [SubTypes.toList, List.getElem?_cons_zero] at hget
          have hc : head = candidate := Option.some.inj hget
          subst candidate
          simpa using hst.rawSourceSupersBeforeA hsyn.1
      | succ k =>
          simp only [SubTypes.toList, List.getElem?_cons_succ] at hget
          have hpositive : 0 < SubTypes.length tail := by
            rw [← SubTypes.toList_length]
            exact Nat.zero_lt_of_lt
              (List.getElem?_eq_some_iff.mp hget).1
          change x.val + (SubTypes.length tail + 1) ≤ 2 ^ 32 at hrange
          have hxlt : x.val + 1 < 2 ^ 32 := by omega
          have hxval : (TypeIdx.ofNat (x.val + 1)).val = x.val + 1 :=
            TypeIdx.ofNat_val_of_lt _ hxlt
          have htailRange :
              (TypeIdx.ofNat (x.val + 1)).val + SubTypes.length tail ≤
                2 ^ 32 := by
            rw [hxval]
            omega
          have hresult := Rectype_ok2A.rawSourceSupersBeforeAt
            htailRange hsyn.2 htail hget
          rw [hxval] at hresult
          rw [show x.val + 1 + k = x.val + (k + 1) by omega] at hresult
          exact hresult
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

private theorem Rectype_okA.rawSourceSupersBeforeAt
    {C : Context} {sts : SubTypes} {x : TypeIdx}
    (hrange : x.val + SubTypes.length sts ≤ 2 ^ 32)
    (hsyn : (RecType.recr sts).isSyn = true)
    (h : Rectype_okA C (.recr sts) x) :
    ∀ {k : Nat} {st : SubType},
      (SubTypes.toList sts)[k]? = some st →
      RawSourceSupersBeforeA C (x.val + k) st := by
  cases h with
  | empty =>
      intro k st hget
      simp [SubTypes.toList] at hget
  | @cons C' head tail x hst _ htail =>
      rw [RecType.isSyn, SubTypes.toList, List.all_cons,
        Bool.and_eq_true] at hsyn
      intro k candidate hget
      cases k with
      | zero =>
          simp only [SubTypes.toList, List.getElem?_cons_zero] at hget
          have hc : head = candidate := Option.some.inj hget
          subst candidate
          simpa using hst.rawSourceSupersBeforeA
      | succ k =>
          simp only [SubTypes.toList, List.getElem?_cons_succ] at hget
          have hpositive : 0 < SubTypes.length tail := by
            rw [← SubTypes.toList_length]
            exact Nat.zero_lt_of_lt
              (List.getElem?_eq_some_iff.mp hget).1
          change x.val + (SubTypes.length tail + 1) ≤ 2 ^ 32 at hrange
          have hxlt : x.val + 1 < 2 ^ 32 := by omega
          have hxval : (TypeIdx.ofNat (x.val + 1)).val = x.val + 1 :=
            TypeIdx.ofNat_val_of_lt _ hxlt
          have htailRange :
              (TypeIdx.ofNat (x.val + 1)).val + SubTypes.length tail ≤
                2 ^ 32 := by
            rw [hxval]
            omega
          have hresult := Rectype_okA.rawSourceSupersBeforeAt
            htailRange hsyn.2 htail hget
          rw [hxval] at hresult
          rw [show x.val + 1 + k = x.val + (k + 1) by omega] at hresult
          exact hresult
  | @rec2 C' all x hrec =>
      intro k st hget
      have hh := Rectype_ok2A.rawSourceSupersBeforeAt
        hrange hsyn hrec hget
      simpa [RawSourceSupersBeforeA, Context.withRecs] using hh
termination_by SubTypes.length sts
decreasing_by simp_all [SubTypes.length]

theorem TypeUse.RankedRerollOriginA.sourceNode
    {E : Context} {base : TypeIdx} {n r : Nat}
    {source target : TypeUse}
    (h : TypeUse.RankedRerollOriginA E base n source target r) :
    E.SourceTypeNodeA (.use source) r := by
  cases h with
  | idx_prefix _ hlookup => exact .idx hlookup
  | idx_current _ _ hlookup => exact .idx hlookup
  | defd_prefix _ hlookup => exact .defd hlookup
  | defd_current _ hlookup => exact .defd hlookup

theorem TypeUse.RankedRerollOriginA.origin
    {E : Context} {base : TypeIdx} {n r : Nat}
    {source target : TypeUse}
    (h : TypeUse.RankedRerollOriginA E base n source target r) :
    TypeUse.RerollOriginA E base n source target := by
  cases h with
  | idx_prefix hprefix _ =>
      exact .idx_out (fun hrange => by omega)
  | idx_current hlo hhi _ => exact .idx_in hlo hhi
  | defd_prefix _ _ => exact .defd_keep _
  | defd_current hi hlookup => exact .defd_at hi hlookup

theorem Context.SourceTypeNodeA.rankedRerollOrigin
    {E : Context} {base : TypeIdx} {n r : Nat} {source : TypeUse}
    (hnode : E.SourceTypeNodeA (.use source) r)
    (hrank : r < 2 * (base.val + n)) :
    ∃ target : TypeUse,
      TypeUse.RankedRerollOriginA E base n source target r := by
  cases hnode with
  | @idx x dt hlookup =>
      by_cases hprefix : x.val < base.val
      · exact ⟨.idx x, .idx_prefix hprefix hlookup⟩
      · have hlo : base.val ≤ x.val := Nat.le_of_not_gt hprefix
        have hhi : x.val < base.val + n := by omega
        exact ⟨.recu (x.val - base.val), .idx_current hlo hhi hlookup⟩
  | @defd i dt hlookup =>
      by_cases hprefix : i < base.val
      · exact ⟨.defd dt, .defd_prefix hprefix hlookup⟩
      · have hlo : base.val ≤ i := Nat.le_of_not_gt hprefix
        have hi : i - base.val < n := by omega
        refine ⟨.recu (i - base.val), ?_⟩
        have heq : base.val + (i - base.val) = i := Nat.add_sub_of_le hlo
        simpa [heq] using
          (TypeUse.RankedRerollOriginA.defd_current
            (E := E) (base := base) hi (by simpa [heq] using hlookup))

/-- A declared-super step from a prefix literal remains entirely in the
prefix.  The source graph's strict rank decrease is what rules out an
accidental equal current-group literal. -/
theorem TypeUse.RankedRerollOriginA.prefixSuper
    {E R : Context} {base : TypeIdx} {n i : Nat} {dt : DefType}
    (hprefix : i < base.val) (hlookup : E.types[i]? = some dt)
    (hgraph : E.SourceTypeGraphOkA) (htypes : R.types = E.types)
    {g : HeapType} (hmem : g ∈ E.heapSupers (.use (.defd dt))) :
    ∃ (sourceTarget targetTarget : TypeUse) (s : Nat),
      g = .use sourceTarget ∧ s < 2 * i ∧
      TypeUse.RankedRerollOriginA E base n sourceTarget targetTarget s ∧
      Heaptype_subA R (.use (.defd dt)) (.use targetTarget) := by
  obtain ⟨s, hslt, hnode⟩ :=
    hgraph (Context.SourceTypeNodeA.defd hlookup) g hmem
  have hmemR : g ∈ R.heapSupers (.use (.defd dt)) := by
    rw [Context.heapSupers_eq_of_types_eq htypes]
    exact hmem
  cases hnode with
  | @idx x targetDt htargetLookup =>
      have hxPrefix : x.val < base.val := by omega
      have htargetLookupR : R.types[x.val]? = some targetDt := by
        simpa [htypes] using htargetLookup
      refine ⟨.idx x, .idx x, 2 * x.val + 1, rfl, hslt,
        .idx_prefix hxPrefix htargetLookup, ?_⟩
      apply Heaptype_subA.typeidx_r htargetLookupR
      exact heapSupers_sound hmemR
        (Heaptype_subA.typeidx_l htargetLookupR .refl)
  | @defd j targetDt htargetLookup =>
      have hjPrefix : j < base.val := by omega
      refine ⟨.defd targetDt, .defd targetDt, 2 * j, rfl, hslt,
        .defd_prefix hjPrefix htargetLookup, ?_⟩
      exact heapSupers_sound hmemR .refl

/-- Dereferencing a ranked source index preserves its exact vector origin:
a prefix index steps to the same prefix literal, while a current index and
its stored literal both denote the same target `REC`. -/
theorem TypeUse.RankedRerollOriginA.idxSuper
    {E R : Context} {base : TypeIdx} {n r : Nat} {x : TypeIdx}
    {target : TypeUse}
    (horigin : TypeUse.RankedRerollOriginA E base n (.idx x) target r)
    (htypes : R.types = E.types) {g : HeapType}
    (hmem : g ∈ E.heapSupers (.use (.idx x))) :
    ∃ (sourceTarget targetTarget : TypeUse) (s : Nat),
      g = .use sourceTarget ∧ s < r ∧
      TypeUse.RankedRerollOriginA E base n sourceTarget targetTarget s ∧
      Heaptype_subA R (.use target) (.use targetTarget) := by
  cases horigin with
  | @idx_prefix _ dt hprefix hlookup =>
      simp only [Context.heapSupers, hlookup, List.mem_singleton] at hmem
      subst g
      have hlookupR : R.types[x.val]? = some dt := by
        simpa [htypes] using hlookup
      exact ⟨.defd dt, .defd dt, 2 * x.val, rfl, by omega,
        .defd_prefix hprefix hlookup,
        Heaptype_subA.typeidx_l hlookupR .refl⟩
  | @idx_current _ dt hlo hhi hlookup =>
      simp only [Context.heapSupers, hlookup, List.mem_singleton] at hmem
      subst g
      have hi : x.val - base.val < n := by omega
      have heq : base.val + (x.val - base.val) = x.val :=
        Nat.add_sub_of_le hlo
      refine ⟨.defd dt, .recu (x.val - base.val), 2 * x.val,
        rfl, by omega, ?_, .refl⟩
      simpa [heq] using
        (TypeUse.RankedRerollOriginA.defd_current
          (E := E) (base := base) hi (by simpa [heq] using hlookup))

theorem TypeUse.RerollOriginA.roll_idx
    (E : Context) (base x : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) :
    TypeUse.RerollOriginA E base n (.idx x)
      (substTypeUse (.idx x) (rollTVars base n) (rollTUses n)) := by
  simp only [substTypeUse, rollTVars, rollTUses]
  rw [substTypeVar_rollVars base x n hbound]
  split
  · rename_i hrange
    exact .idx_in hrange.1 hrange.2
  · rename_i hout
    exact .idx_out hout

theorem TypeUse.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {tu : TypeUse}
    (hfree : TypesBelow base.val (freeTypeUse tu)) :
    TypeUse.RerollOriginA E base n tu tu := by
  cases tu with
  | idx x =>
      apply TypeUse.RerollOriginA.idx_out
      intro hrange
      have hx : x.val < base.val := hfree x (by
        simp [freeTypeUse, Free.ofTypeIdx])
      omega
  | recu i => exact .recu i
  | defd dt => exact .defd_keep dt

theorem HeapType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {ht : HeapType}
    (hfree : TypesBelow base.val (freeHeapType ht)) :
    HeapType.RerollOriginA E base n ht ht := by
  cases ht with
  | abs a => exact .abs a
  | use tu => exact .use (TypeUse.RerollOriginA.keep
      (by simpa [freeHeapType] using hfree))

theorem TypeUse.RerollOriginA.target_eq_of_syn
    {E : Context} {base : TypeIdx} {n : Nat}
    {source target₁ target₂ : TypeUse}
    (hsyn : source.isSyn = true)
    (h₁ : TypeUse.RerollOriginA E base n source target₁)
    (h₂ : TypeUse.RerollOriginA E base n source target₂) :
    target₁ = target₂ := by
  cases source with
  | recu i => simp [TypeUse.isSyn] at hsyn
  | defd dt => simp [TypeUse.isSyn] at hsyn
  | idx x =>
      cases h₁ with
      | idx_in hlo₁ hhi₁ =>
          cases h₂ with
          | idx_in _ _ => rfl
          | idx_out hout₂ => exact False.elim (hout₂ ⟨hlo₁, hhi₁⟩)
      | idx_out hout₁ =>
          cases h₂ with
          | idx_in hlo₂ hhi₂ => exact False.elim (hout₁ ⟨hlo₂, hhi₂⟩)
          | idx_out _ => rfl

theorem HeapType.RerollOriginA.target_eq_of_syn
    {E : Context} {base : TypeIdx} {n : Nat}
    {source target₁ target₂ : HeapType}
    (hsyn : source.isSyn = true)
    (h₁ : HeapType.RerollOriginA E base n source target₁)
    (h₂ : HeapType.RerollOriginA E base n source target₂) :
    target₁ = target₂ := by
  cases source with
  | abs a => cases h₁; cases h₂; rfl
  | use tu =>
      cases h₁ with
      | use h₁ =>
          cases h₂ with
          | use h₂ =>
              exact congrArg HeapType.use
                (TypeUse.RerollOriginA.target_eq_of_syn hsyn h₁ h₂)

theorem RefType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {rt : RefType}
    (hfree : TypesBelow base.val (freeRefType rt)) :
    RefType.RerollOriginA E base n rt rt := by
  cases rt with
  | ref nul ht =>
      exact .ref (HeapType.RerollOriginA.keep
        (by simpa [freeRefType] using hfree))

theorem ValType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {t : ValType}
    (hfree : TypesBelow base.val (freeValType t)) :
    ValType.RerollOriginA E base n t t := by
  cases t with
  | num nt => exact .num nt
  | vec vt => exact .vec vt
  | bot => exact .bot
  | ref rt =>
      exact .ref (RefType.RerollOriginA.keep
        (by simpa [freeValType] using hfree))

theorem StorageType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {zt : StorageType}
    (hfree : TypesBelow base.val (freeStorageType zt)) :
    StorageType.RerollOriginA E base n zt zt := by
  cases zt with
  | pack pt => exact .pack pt
  | val t =>
      exact .val (ValType.RerollOriginA.keep
        (by simpa [freeStorageType] using hfree))

theorem FieldType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {ft : FieldType}
    (hfree : TypesBelow base.val (freeFieldType ft)) :
    FieldType.RerollOriginA E base n ft ft := by
  cases ft with
  | mk mutability zt =>
      exact .mk (StorageType.RerollOriginA.keep
        (by simpa [freeFieldType] using hfree))

private theorem FieldTypes.RerollOriginA.keep : ∀ (fts : FieldTypes)
    {E : Context} {base : TypeIdx} {n : Nat},
    TypesBelow base.val (freeFieldTypes fts) →
    FieldTypes.RerollOriginA E base n fts fts := by
  intro fts
  cases fts with
  | nil => intros; exact .nil
  | cons ft rest =>
      intro E base n hfree
      rw [freeFieldTypes, typesBelow_append] at hfree
      exact .cons (FieldType.RerollOriginA.keep hfree.1)
        (FieldTypes.RerollOriginA.keep rest hfree.2)

private theorem ValTypes.RerollOriginA.keep : ∀ (ts : ValTypes)
    {E : Context} {base : TypeIdx} {n : Nat},
    TypesBelow base.val (freeValTypes ts) →
    ValTypes.RerollOriginA E base n ts ts := by
  intro ts
  cases ts with
  | nil => intros; exact .nil
  | cons t rest =>
      intro E base n hfree
      rw [freeValTypes, typesBelow_append] at hfree
      exact .cons (ValType.RerollOriginA.keep hfree.1)
        (ValTypes.RerollOriginA.keep rest hfree.2)

theorem CompType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {ct : CompType}
    (hfree : TypesBelow base.val (freeCompType ct)) :
    CompType.RerollOriginA E base n ct ct := by
  cases ct with
  | struct fields =>
      exact .struct (FieldTypes.RerollOriginA.keep fields
        (by simpa [freeCompType] using hfree))
  | array field =>
      exact .array (FieldType.RerollOriginA.keep
        (by simpa [freeCompType] using hfree))
  | func dom cod =>
      rw [freeCompType, typesBelow_append] at hfree
      exact .func (ValTypes.RerollOriginA.keep dom hfree.1)
        (ValTypes.RerollOriginA.keep cod hfree.2)

private theorem TypeUses.RerollOriginA.keep : ∀ (sups : TypeUses)
    {E : Context} {base : TypeIdx} {n : Nat},
    TypesBelow base.val (freeTypeUses sups) →
    TypeUses.RerollOriginA E base n sups sups := by
  intro sups
  cases sups with
  | nil => intros; exact .nil
  | cons tu rest =>
      intro E base n hfree
      rw [freeTypeUses, typesBelow_append] at hfree
      exact .cons (TypeUse.RerollOriginA.keep hfree.1)
        (TypeUses.RerollOriginA.keep rest hfree.2)

theorem SubType.RerollOriginA.keep
    {E : Context} {base : TypeIdx} {n : Nat} {st : SubType}
    (hfree : TypesBelow base.val (freeSubType st)) :
    SubType.RerollOriginA E base n st st := by
  cases st with
  | sub fin sups ct =>
      rw [freeSubType, typesBelow_append] at hfree
      exact .sub (TypeUses.RerollOriginA.keep sups hfree.1)
        (CompType.RerollOriginA.keep hfree.2)

theorem HeapType.RerollOriginA.roll
    {ht : HeapType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ht.isSyn = true) :
    HeapType.RerollOriginA E base n ht
      (substHeapType ht (rollTVars base n) (rollTUses n)) := by
  cases ht with
  | abs a => exact .abs a
  | use tu =>
      cases tu with
      | idx x => exact .use (TypeUse.RerollOriginA.roll_idx E base x n hbound)
      | recu i => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | defd dt => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

theorem RefType.RerollOriginA.roll
    {rt : RefType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : rt.isSyn = true) :
    RefType.RerollOriginA E base n rt
      (substRefType rt (rollTVars base n) (rollTUses n)) := by
  cases rt with
  | ref nul ht => exact .ref (HeapType.RerollOriginA.roll E base n hbound hsyn)

theorem ValType.RerollOriginA.roll
    {t : ValType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : t.isSyn = true) :
    ValType.RerollOriginA E base n t
      (substValType t (rollTVars base n) (rollTUses n)) := by
  cases t with
  | num nt => exact .num nt
  | vec vt => exact .vec vt
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt => exact .ref (RefType.RerollOriginA.roll E base n hbound hsyn)

theorem StorageType.RerollOriginA.roll
    {zt : StorageType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : zt.isSyn = true) :
    StorageType.RerollOriginA E base n zt
      (substStorageType zt (rollTVars base n) (rollTUses n)) := by
  cases zt with
  | pack pt => exact .pack pt
  | val t => exact .val (ValType.RerollOriginA.roll E base n hbound hsyn)

theorem FieldType.RerollOriginA.roll
    {ft : FieldType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ft.isSyn = true) :
    FieldType.RerollOriginA E base n ft
      (substFieldType ft (rollTVars base n) (rollTUses n)) := by
  cases ft with
  | mk mutability zt =>
      exact .mk (StorageType.RerollOriginA.roll E base n hbound hsyn)

private theorem FieldTypes.RerollOriginA.roll : ∀ (fts : FieldTypes)
    (E : Context) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    FieldTypes.RerollOriginA E base n fts
      (substFieldTypes fts (rollTVars base n) (rollTUses n)) := by
  intro fts
  cases fts with
  | nil => intros; exact .nil
  | cons ft rest =>
      intro E base n hbound hsyn
      simp only [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      exact .cons
        (FieldType.RerollOriginA.roll E base n hbound hsyn.1)
        (FieldTypes.RerollOriginA.roll rest E base n hbound hsyn.2)

private theorem ValTypes.RerollOriginA.roll : ∀ (ts : ValTypes)
    (E : Context) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (ValTypes.toList ts).all ValType.isSyn = true →
    ValTypes.RerollOriginA E base n ts
      (substValTypes ts (rollTVars base n) (rollTUses n)) := by
  intro ts
  cases ts with
  | nil => intros; exact .nil
  | cons t rest =>
      intro E base n hbound hsyn
      simp only [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      exact .cons
        (ValType.RerollOriginA.roll E base n hbound hsyn.1)
        (ValTypes.RerollOriginA.roll rest E base n hbound hsyn.2)

theorem CompType.RerollOriginA.roll
    {ct : CompType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ct.isSyn = true) :
    CompType.RerollOriginA E base n ct
      (substCompType ct (rollTVars base n) (rollTUses n)) := by
  cases ct with
  | struct fields =>
      exact .struct
        (FieldTypes.RerollOriginA.roll fields E base n hbound hsyn)
  | array field =>
      exact .array (FieldType.RerollOriginA.roll E base n hbound hsyn)
  | func dom cod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      exact .func
        (ValTypes.RerollOriginA.roll dom E base n hbound hsyn.1)
        (ValTypes.RerollOriginA.roll cod E base n hbound hsyn.2)

private theorem TypeUses.RerollOriginA.roll : ∀ (sups : TypeUses)
    (E : Context) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (TypeUses.toList sups).all TypeUse.isSyn = true →
    TypeUses.RerollOriginA E base n sups
      (substTypeUses sups (rollTVars base n) (rollTUses n)) := by
  intro sups
  cases sups with
  | nil => intros; exact .nil
  | cons tu rest =>
      intro E base n hbound hsyn
      simp only [TypeUses.toList, List.all_cons, Bool.and_eq_true] at hsyn
      cases tu with
      | idx x =>
          exact TypeUses.RerollOriginA.cons
            (TypeUse.RerollOriginA.roll_idx E base x n hbound)
            (TypeUses.RerollOriginA.roll rest E base n hbound hsyn.2)
      | recu i => simp [TypeUse.isSyn] at hsyn
      | defd dt => simp [TypeUse.isSyn] at hsyn

theorem SubType.RerollOriginA.roll
    {st : SubType} (E : Context) (base : TypeIdx) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : st.isSyn = true) :
    SubType.RerollOriginA E base n st
      (substSubType st (rollTVars base n) (rollTUses n)) := by
  cases st with
  | sub fin sups ct =>
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      exact .sub
        (TypeUses.RerollOriginA.roll sups E base n hbound hsyn.1)
        (CompType.RerollOriginA.roll E base n hbound hsyn.2)

private theorem SubTypes.RerollOriginA.roll : ∀ (sts : SubTypes)
    (E : Context) (base : TypeIdx) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (SubTypes.toList sts).all SubType.isSyn = true →
    SubTypes.RerollOriginA E base n sts
      (substSubTypes sts (rollTVars base n) (rollTUses n)) := by
  intro sts
  cases sts with
  | nil => intros; exact .nil
  | cons st rest =>
      intro E base n hbound hsyn
      simp only [SubTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      exact .cons
        (SubType.RerollOriginA.roll E base n hbound hsyn.1)
        (SubTypes.RerollOriginA.roll rest E base n hbound hsyn.2)

theorem RecType.RerollOriginA.roll
    {qt : RecType} (E : Context) (base : TypeIdx)
    (hbound : base.val + qt.count ≤ 2 ^ 32) (hsyn : qt.isSyn = true) :
    RecType.RerollOriginA E base qt.count qt (rollRt base qt) := by
  cases qt with
  | recr sts =>
      exact .recr (SubTypes.RerollOriginA.roll sts E base
        (SubTypes.length sts)
        (by simpa [RecType.count] using hbound)
        (by simpa [RecType.isSyn] using hsyn))

/-- The provenance-sensitive counterpart of `reroll_rollUnroll_idx`.  The
lookup family identifies the current group's canonical stored entries; an
equal literal at a different index is never selected implicitly. -/
theorem TypeUse.RerollOriginA.rollUnroll_idx
    {E : Context} (base x : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i)) :
    TypeUse.RerollOriginA E base n
      (substTypeUse
        (substTypeUse (.idx x) (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substTypeUse (.idx x) (rollTVars base n) (rollTUses n)) := by
  simp only [substTypeUse, rollTVars, rollTUses]
  rw [substTypeVar_rollVars base x n hbound]
  split
  · rename_i hrange
    simp only [substTypeUse, recvTVars, unrollTUses]
    rw [substTypeVar_unrollRecVars]
    have hoff : x.val - base.val < n := by omega
    rw [if_pos hoff]
    exact .defd_at hoff (by
      simpa [Nat.add_sub_of_le hrange.1] using hgroup (x.val - base.val) hoff)
  · rename_i hout
    simp only [substTypeUse, recvTVars, unrollTUses]
    rw [substTypeVar_unrollIdxVars]
    exact .idx_out hout

/-- The same roll/unroll calculation with the declaration-site ordering
evidence retained.  The lookup of the raw `_IDX` is used only in the prefix
branch; a current-group occurrence is tied to its canonical stored member by
`hgroup`. -/
theorem TypeUse.RerollBeforeA.rollUnroll_idx
    {E : Context} (base y : TypeIdx) (qt : RecType) (n i : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hi : i < n)
    (hy : y.val < base.val + i) {dt : DefType}
    (hyLookup : E.types[y.val]? = some dt)
    (hgroup : ∀ j : Nat, j < n →
      E.types[base.val + j]? = some (.defd (rollRt base qt) j)) :
    TypeUse.RerollBeforeA E base n i
      (substTypeUse
        (substTypeUse (.idx y) (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substTypeUse (.idx y) (rollTVars base n) (rollTUses n)) := by
  simp only [substTypeUse, rollTVars, rollTUses]
  rw [substTypeVar_rollVars base y n hbound]
  split
  · rename_i hrange
    simp only [substTypeUse, recvTVars, unrollTUses]
    rw [substTypeVar_unrollRecVars]
    have hj : y.val - base.val < n := by omega
    rw [if_pos hj]
    exact .defd_current (by omega) hj (by
      simpa [Nat.add_sub_of_le hrange.1] using
        hgroup (y.val - base.val) hj)
  · rename_i hout
    simp only [substTypeUse, recvTVars, unrollTUses]
    rw [substTypeVar_unrollIdxVars]
    exact .idx_prefix (by omega) hyLookup

theorem HeapType.RerollOriginA.rollUnroll
    {E : Context} {ht : HeapType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : ht.isSyn = true) :
    HeapType.RerollOriginA E base n
      (substHeapType
        (substHeapType ht (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substHeapType ht (rollTVars base n) (rollTUses n)) := by
  cases ht with
  | abs a => exact .abs a
  | use tu =>
      cases tu with
      | idx x =>
          exact HeapType.RerollOriginA.use
            (TypeUse.RerollOriginA.rollUnroll_idx
              base x qt n hbound hgroup)
      | recu i => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | defd dt => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

theorem RefType.RerollOriginA.rollUnroll
    {E : Context} {rt : RefType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : rt.isSyn = true) :
    RefType.RerollOriginA E base n
      (substRefType
        (substRefType rt (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substRefType rt (rollTVars base n) (rollTUses n)) := by
  cases rt with
  | ref nul ht =>
      exact RefType.RerollOriginA.ref
        (HeapType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn)

theorem ValType.RerollOriginA.rollUnroll
    {E : Context} {t : ValType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : t.isSyn = true) :
    ValType.RerollOriginA E base n
      (substValType
        (substValType t (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substValType t (rollTVars base n) (rollTUses n)) := by
  cases t with
  | num nt => exact .num nt
  | vec vt => exact .vec vt
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt =>
      exact ValType.RerollOriginA.ref
        (RefType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn)

theorem StorageType.RerollOriginA.rollUnroll
    {E : Context} {zt : StorageType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : zt.isSyn = true) :
    StorageType.RerollOriginA E base n
      (substStorageType
        (substStorageType zt (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substStorageType zt (rollTVars base n) (rollTUses n)) := by
  cases zt with
  | pack pt => exact .pack pt
  | val t =>
      exact StorageType.RerollOriginA.val
        (ValType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn)

theorem FieldType.RerollOriginA.rollUnroll
    {E : Context} {ft : FieldType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : ft.isSyn = true) :
    FieldType.RerollOriginA E base n
      (substFieldType
        (substFieldType ft (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substFieldType ft (rollTVars base n) (rollTUses n)) := by
  cases ft with
  | mk mutability zt =>
      exact FieldType.RerollOriginA.mk
        (StorageType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn)

private theorem FieldTypes.RerollOriginA.rollUnroll : ∀ (fts : FieldTypes)
    {E : Context} (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i)) →
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    FieldTypes.RerollOriginA E base n
      (substFieldTypes
        (substFieldTypes fts (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substFieldTypes fts (rollTVars base n) (rollTUses n)) := by
  intro fts
  cases fts with
  | nil => intros; exact .nil
  | cons ft rest =>
      intro E base qt n hbound hgroup hsyn
      simp only [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      exact .cons
        (FieldType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn.1)
        (FieldTypes.RerollOriginA.rollUnroll rest base qt n hbound
          hgroup hsyn.2)

private theorem ValTypes.RerollOriginA.rollUnroll : ∀ (ts : ValTypes)
    {E : Context} (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i)) →
    (ValTypes.toList ts).all ValType.isSyn = true →
    ValTypes.RerollOriginA E base n
      (substValTypes
        (substValTypes ts (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substValTypes ts (rollTVars base n) (rollTUses n)) := by
  intro ts
  cases ts with
  | nil => intros; exact .nil
  | cons t rest =>
      intro E base qt n hbound hgroup hsyn
      simp only [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      exact .cons
        (ValType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn.1)
        (ValTypes.RerollOriginA.rollUnroll rest base qt n hbound
          hgroup hsyn.2)

theorem CompType.RerollOriginA.rollUnroll
    {E : Context} {ct : CompType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : ct.isSyn = true) :
    CompType.RerollOriginA E base n
      (substCompType
        (substCompType ct (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substCompType ct (rollTVars base n) (rollTUses n)) := by
  cases ct with
  | struct fields =>
      exact CompType.RerollOriginA.struct
        (FieldTypes.RerollOriginA.rollUnroll fields base qt n hbound
          hgroup hsyn)
  | array field =>
      exact CompType.RerollOriginA.array
        (FieldType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn)
  | func dom cod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      exact CompType.RerollOriginA.func
        (ValTypes.RerollOriginA.rollUnroll dom base qt n hbound
          hgroup hsyn.1)
        (ValTypes.RerollOriginA.rollUnroll cod base qt n hbound
          hgroup hsyn.2)

private theorem TypeUses.RerollOriginA.rollUnroll : ∀ (sups : TypeUses)
    {E : Context} (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i)) →
    (TypeUses.toList sups).all TypeUse.isSyn = true →
    TypeUses.RerollOriginA E base n
      (substTypeUses
        (substTypeUses sups (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substTypeUses sups (rollTVars base n) (rollTUses n)) := by
  intro sups
  cases sups with
  | nil => intros; exact .nil
  | cons tu rest =>
      intro E base qt n hbound hgroup hsyn
      simp only [TypeUses.toList, List.all_cons, Bool.and_eq_true] at hsyn
      cases tu with
      | idx x =>
          exact TypeUses.RerollOriginA.cons
            (TypeUse.RerollOriginA.rollUnroll_idx
              base x qt n hbound hgroup)
            (TypeUses.RerollOriginA.rollUnroll rest base qt n hbound
              hgroup hsyn.2)
      | recu i => simp [TypeUse.isSyn] at hsyn
      | defd dt => simp [TypeUse.isSyn] at hsyn

theorem SubType.RerollOriginA.rollUnroll
    {E : Context} {st : SubType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : st.isSyn = true) :
    SubType.RerollOriginA E base n
      (substSubType
        (substSubType st (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substSubType st (rollTVars base n) (rollTUses n)) := by
  cases st with
  | sub fin sups ct =>
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      exact .sub
        (TypeUses.RerollOriginA.rollUnroll sups base qt n hbound
          hgroup hsyn.1)
        (CompType.RerollOriginA.rollUnroll base qt n hbound
          hgroup hsyn.2)

private theorem SubTypes.RerollOriginA.rollUnroll : ∀ (sts : SubTypes)
    {E : Context} (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i)) →
    (SubTypes.toList sts).all SubType.isSyn = true →
    SubTypes.RerollOriginA E base n
      (substSubTypes
        (substSubTypes sts (rollTVars base n) (rollTUses n))
        (recvTVars n) (unrollTUses (rollRt base qt) n))
      (substSubTypes sts (rollTVars base n) (rollTUses n)) := by
  intro sts
  cases sts with
  | nil => intros; exact .nil
  | cons st rest =>
      intro E base qt n hbound hgroup hsyn
      simp only [SubTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      exact .cons
        (SubType.RerollOriginA.rollUnroll base qt n hbound hgroup hsyn.1)
        (SubTypes.RerollOriginA.rollUnroll rest base qt n hbound
          hgroup hsyn.2)

theorem RecType.RerollOriginA.rollUnroll
    {E : Context} {qt : RecType} (base : TypeIdx)
    (hbound : base.val + qt.count ≤ 2 ^ 32)
    (hgroup : ∀ i : Nat, i < qt.count →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i))
    (hsyn : qt.isSyn = true) :
    RecType.RerollOriginA E base qt.count
      (unrollRt (rollRt base qt)) (rollRt base qt) := by
  cases qt with
  | recr sts =>
      simp only [rollRt, unrollRt, SubTypes.length_substSubTypes,
        RecType.count]
      exact .recr
        (SubTypes.RerollOriginA.rollUnroll sts base (.recr sts)
          (SubTypes.length sts)
          (by simpa [RecType.count] using hbound)
          (by simpa [RecType.count] using hgroup)
          (by simpa [RecType.isSyn] using hsyn))

theorem TypeUses.RerollOriginA.getElem
    {E : Context} {base : TypeIdx} {n j : Nat}
    {source target : TypeUses} {sourceUse targetUse : TypeUse}
    (h : TypeUses.RerollOriginA E base n source target)
    (hsource : (TypeUses.toList source)[j]? = some sourceUse)
    (htarget : (TypeUses.toList target)[j]? = some targetUse) :
    TypeUse.RerollOriginA E base n sourceUse targetUse := by
  induction h generalizing j sourceUse targetUse with
  | nil => simp [TypeUses.toList] at hsource
  | cons hhead htail ih =>
      cases j with
      | zero =>
          simp only [TypeUses.toList, List.getElem?_cons_zero,
            Option.some.injEq] at hsource htarget
          subst sourceUse
          subst targetUse
          exact hhead
      | succ j =>
          simp only [TypeUses.toList, List.getElem?_cons_succ] at hsource htarget
          exact ih hsource htarget

theorem TypeUses.RerollOriginA.length_eq
    {E : Context} {base : TypeIdx} {n : Nat}
    {source target : TypeUses}
    (h : TypeUses.RerollOriginA E base n source target) :
    (TypeUses.toList source).length = (TypeUses.toList target).length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa [TypeUses.toList] using congrArg Nat.succ ih

theorem SubTypes.RerollOriginA.getElem
    {E : Context} {base : TypeIdx} {n j : Nat}
    {source target : SubTypes} {sourceType targetType : SubType}
    (h : SubTypes.RerollOriginA E base n source target)
    (hsource : (SubTypes.toList source)[j]? = some sourceType)
    (htarget : (SubTypes.toList target)[j]? = some targetType) :
    SubType.RerollOriginA E base n sourceType targetType := by
  induction h generalizing j sourceType targetType with
  | nil => simp [SubTypes.toList] at hsource
  | cons hhead htail ih =>
      cases j with
      | zero =>
          simp only [SubTypes.toList, List.getElem?_cons_zero,
            Option.some.injEq] at hsource htarget
          subst sourceType
          subst targetType
          exact hhead
      | succ j =>
          simp only [SubTypes.toList, List.getElem?_cons_succ] at hsource htarget
          exact ih hsource htarget

theorem SubTypes.RerollOriginA.length_eq
    {E : Context} {base : TypeIdx} {n : Nat}
    {source target : SubTypes}
    (h : SubTypes.RerollOriginA E base n source target) :
    (SubTypes.toList source).length = (SubTypes.toList target).length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa [SubTypes.toList] using congrArg Nat.succ ih

theorem SubTypes.RerollOriginA.getElem_sub
    {E : Context} {base : TypeIdx} {n i : Nat}
    {source target : SubTypes} {fin : Option Final}
    {sourceSups : TypeUses} {sourceComp : CompType}
    (h : SubTypes.RerollOriginA E base n source target)
    (hsource : (SubTypes.toList source)[i]? =
      some (.sub fin sourceSups sourceComp)) :
    ∃ (targetSups : TypeUses) (targetComp : CompType),
      (SubTypes.toList target)[i]? =
        some (.sub fin targetSups targetComp) ∧
      TypeUses.RerollOriginA E base n sourceSups targetSups ∧
      CompType.RerollOriginA E base n sourceComp targetComp := by
  induction h generalizing i fin sourceSups sourceComp with
  | nil => simp [SubTypes.toList] at hsource
  | @cons sourceHead targetHead sourceTail targetTail hhead htail ih =>
      cases i with
      | zero =>
          simp only [SubTypes.toList, List.getElem?_cons_zero,
            Option.some.injEq] at hsource
          subst sourceHead
          cases hhead with
          | sub hsupers hcomp =>
              exact ⟨_, _, by simp [SubTypes.toList], hsupers, hcomp⟩
      | succ i =>
          simp only [SubTypes.toList, List.getElem?_cons_succ] at hsource
          obtain ⟨targetSups, targetComp, htarget, hsupers, hcomp⟩ :=
            ih hsource
          exact ⟨targetSups, targetComp,
            by simpa [SubTypes.toList] using htarget, hsupers, hcomp⟩

/-- A matched current-group member exposes matched declared supertypes, and
the target occurrence is an actual amended `REC` edge in the target scratch
context. -/
theorem SubTypes.RerollOriginA.recuSuper
    {E R : Context} {base : TypeIdx} {n i j : Nat}
    {sourceGroup targetGroup : SubTypes}
    {fin : Option Final} {sourceSups targetSups : TypeUses}
    {sourceComp targetComp : CompType}
    {sourceSuper targetSuper : TypeUse}
    (hgroup : SubTypes.RerollOriginA E base n sourceGroup targetGroup)
    (hsourceMember : (SubTypes.toList sourceGroup)[i]? =
      some (.sub fin sourceSups sourceComp))
    (htargetMember : (SubTypes.toList targetGroup)[i]? =
      some (.sub fin targetSups targetComp))
    (hsourceSuper : (TypeUses.toList sourceSups)[j]? = some sourceSuper)
    (htargetSuper : (TypeUses.toList targetSups)[j]? = some targetSuper)
    (hrecs : R.recs = SubTypes.toList targetGroup) :
    TypeUse.RerollOriginA E base n sourceSuper targetSuper ∧
      Heaptype_subA R (.use (.recu i)) (.use targetSuper) := by
  have hmember := hgroup.getElem hsourceMember htargetMember
  cases hmember with
  | sub hsupers _ =>
      exact ⟨hsupers.getElem hsourceSuper htargetSuper,
        Heaptype_subA.rec_
          (by simpa [hrecs] using htargetMember) htargetSuper⟩

theorem SubTypes.RerollOriginA.recuSuper_of_mem
    {E R : Context} {base : TypeIdx} {n i : Nat}
    {sourceGroup targetGroup : SubTypes}
    {fin : Option Final} {sourceSups : TypeUses}
    {sourceComp : CompType} {sourceSuper : TypeUse}
    (hgroup : SubTypes.RerollOriginA E base n sourceGroup targetGroup)
    (hsourceMember : (SubTypes.toList sourceGroup)[i]? =
      some (.sub fin sourceSups sourceComp))
    (hsourceSuper : sourceSuper ∈ TypeUses.toList sourceSups)
    (hrecs : R.recs = SubTypes.toList targetGroup) :
    ∃ targetSuper : TypeUse,
      TypeUse.RerollOriginA E base n sourceSuper targetSuper ∧
      Heaptype_subA R (.use (.recu i)) (.use targetSuper) := by
  obtain ⟨targetSups, targetComp, htargetMember, hsupers, _⟩ :=
    hgroup.getElem_sub hsourceMember
  obtain ⟨j, hsourceGet⟩ := List.getElem?_of_mem hsourceSuper
  have hjSource : j < (TypeUses.toList sourceSups).length :=
    (List.getElem?_eq_some_iff.mp hsourceGet).1
  have hjTarget : j < (TypeUses.toList targetSups).length := by
    rw [← hsupers.length_eq]
    exact hjSource
  let targetSuper := (TypeUses.toList targetSups)[j]'hjTarget
  have htargetGet : (TypeUses.toList targetSups)[j]? =
      some targetSuper := List.getElem?_eq_getElem hjTarget
  exact ⟨targetSuper,
    hsupers.getElem hsourceGet htargetGet,
    Heaptype_subA.rec_ (by simpa [hrecs] using htargetMember)
      htargetGet⟩

theorem RecType.RerollOriginA.recuSuper_of_heapSuper
    {E R : Context} {base : TypeIdx} {n i : Nat}
    {sourceRec targetRec : RecType}
    (hrec : RecType.RerollOriginA E base n sourceRec targetRec)
    {fin : Option Final} {sourceSups : TypeUses}
    {sourceComp : CompType}
    (hsourceMember : (match sourceRec with
      | .recr sts => SubTypes.toList sts)[i]? =
        some (.sub fin sourceSups sourceComp))
    (hrecs : R.recs = match targetRec with
      | .recr sts => SubTypes.toList sts)
    {g : HeapType}
    (hmem : g ∈ (TypeUses.toList sourceSups).map HeapType.use) :
    ∃ (sourceSuper targetSuper : TypeUse),
      g = .use sourceSuper ∧
      TypeUse.RerollOriginA E base n sourceSuper targetSuper ∧
      Heaptype_subA R (.use (.recu i)) (.use targetSuper) := by
  cases hrec with
  | recr hgroup =>
      obtain ⟨sourceSuper, hsourceSuper, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨targetSuper, horigin, hsub⟩ :=
        hgroup.recuSuper_of_mem hsourceMember hsourceSuper hrecs
      exact ⟨sourceSuper, targetSuper, rfl, horigin, hsub⟩

/-- Positional provenance for every declared-super occurrence in an aligned
recursive group. -/
def RecType.RerollSupersBeforeA
    (E : Context) (base : TypeIdx) (n : Nat)
    (sourceRec targetRec : RecType) : Prop :=
  ∀ (i : Nat) (sourceMember targetMember : SubType),
    (match sourceRec with
      | .recr sts => SubTypes.toList sts)[i]? = some sourceMember →
    (match targetRec with
      | .recr sts => SubTypes.toList sts)[i]? = some targetMember →
    ∀ (sourceSups targetSups : TypeUses)
      (sourceComp targetComp : CompType) (fin : Option Final),
      sourceMember = .sub fin sourceSups sourceComp →
      targetMember = .sub fin targetSups targetComp →
      ∀ (j : Nat) (sourceSuper targetSuper : TypeUse),
        (TypeUses.toList sourceSups)[j]? = some sourceSuper →
        (TypeUses.toList targetSups)[j]? = some targetSuper →
        TypeUse.RerollBeforeA E base n i sourceSuper targetSuper

theorem RecType.RerollSupersBeforeA.rollUnroll
    {B E : Context} {base : TypeIdx} {qt : RecType} {tail : List DefType}
    (htypes : E.types = B.types ++ tail)
    (hbound : base.val + qt.count ≤ 2 ^ 32)
    (hsyn : qt.isSyn = true) (hrect : Rectype_okA B qt base)
    (hgroup : ∀ i : Nat, i < qt.count →
      E.types[base.val + i]? = some (.defd (rollRt base qt) i)) :
    RecType.RerollSupersBeforeA E base qt.count
      (unrollRt (rollRt base qt)) (rollRt base qt) := by
  cases qt with
  | recr rawSts =>
      have hrawSyn : (RecType.recr rawSts).isSyn = true := hsyn
      intro i sourceMember targetMember hsourceMember htargetMember
        sourceSups targetSups sourceComp targetComp fin
        hsourceEq htargetEq j sourceSuper targetSuper
        hsourceSuper htargetSuper
      have hi : i < SubTypes.length rawSts := by
        have hiTarget := (List.getElem?_eq_some_iff.mp htargetMember).1
        simpa [rollRt] using hiTarget
      let rawMember := (SubTypes.toList rawSts)[i]'(by
        simpa only [SubTypes.toList_length] using hi)
      have hrawMember : (SubTypes.toList rawSts)[i]? = some rawMember :=
        List.getElem?_eq_getElem (by
          simpa only [SubTypes.toList_length] using hi)
      have htargetMemberEq :
          substSubType rawMember (rollTVars base (SubTypes.length rawSts))
              (rollTUses (SubTypes.length rawSts)) = targetMember := by
        have ht := htargetMember
        simp only [rollRt, SubTypes.getElem?_substSubTypes,
          hrawMember, Option.map_some, Option.some.injEq] at ht
        exact ht
      have hsourceMemberEq :
          substSubType
              (substSubType rawMember
                (rollTVars base (SubTypes.length rawSts))
                (rollTUses (SubTypes.length rawSts)))
              (recvTVars (SubTypes.length rawSts))
              (unrollTUses (rollRt base (.recr rawSts))
                (SubTypes.length rawSts)) = sourceMember := by
        have hs := hsourceMember
        simp only [rollRt, unrollRt,
          SubTypes.length_substSubTypes,
          SubTypes.getElem?_substSubTypes, hrawMember,
          Option.map_some, Option.some.injEq] at hs
        exact hs
      cases hrawShape : rawMember with
      | sub rawFin rawSups rawComp =>
          have hsourceCombined := hsourceMemberEq.trans hsourceEq
          have htargetCombined := htargetMemberEq.trans htargetEq
          simp only [hrawShape] at hsourceCombined htargetCombined
          obtain ⟨rfl, rfl, rfl⟩ := hsourceCombined
          obtain ⟨rfl, rfl⟩ := htargetCombined
          have hrawBefore := hrect.rawSourceSupersBeforeAt
            (by simpa [RecType.count] using hbound) hrawSyn hrawMember
          rw [hrawShape] at hrawBefore
          have htargetGet := htargetSuper
          simp only [TypeUses.toList_substTypeUses',
            List.getElem?_map] at htargetGet
          obtain ⟨rawSuper, hrawSuper, htargetSuperEq⟩ :=
            Option.map_eq_some_iff.mp htargetGet
          have hsourceGet := hsourceSuper
          simp only [TypeUses.toList_substTypeUses', List.map_map,
            List.getElem?_map, hrawSuper, Option.map_some,
            Option.some.injEq] at hsourceGet
          subst targetSuper
          subst sourceSuper
          obtain ⟨y, dt, hrawSuperEq, hy, hyLookup, _⟩ :=
            hrawBefore rawSuper (List.mem_of_getElem? hrawSuper)
          subst rawSuper
          have hyLen : y.val < B.types.length :=
            (List.getElem?_eq_some_iff.mp hyLookup).1
          have hyLookupE : E.types[y.val]? = some dt := by
            rw [htypes, List.getElem?_append_left hyLen]
            exact hyLookup
          simpa [RecType.count] using
            (TypeUse.RerollBeforeA.rollUnroll_idx
              (E := E) base y (.recr rawSts) (SubTypes.length rawSts) i
              (by simpa [RecType.count] using hbound) hi hy hyLookupE
              (by simpa [RecType.count] using hgroup))

/-- Every one-step edge from a ranked source node is simulated by amended
subtyping in the rerolled scratch context.  The current-literal arm uses the
canonical vector lookup to select the same `REC` member; equal literals at
other positions are irrelevant. -/
theorem TypeUse.RankedRerollOriginA.super
    {E R : Context} {base : TypeIdx} {n r : Nat}
    {source target : TypeUse} {targetRec : RecType}
    (horigin : TypeUse.RankedRerollOriginA E base n source target r)
    (hgraph : E.SourceTypeGraphOkA) (htypes : R.types = E.types)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd targetRec i))
    (hrec : RecType.RerollOriginA E base n
      (unrollRt targetRec) targetRec)
    (hbefore : RecType.RerollSupersBeforeA E base n
      (unrollRt targetRec) targetRec)
    (hrecs : R.recs = match targetRec with
      | .recr sts => SubTypes.toList sts)
    {g : HeapType} (hmem : g ∈ E.heapSupers (.use source)) :
    ∃ (sourceNext targetNext : TypeUse) (s : Nat),
      g = .use sourceNext ∧ s < r ∧
      TypeUse.RankedRerollOriginA E base n sourceNext targetNext s ∧
      Heaptype_subA R (.use target) (.use targetNext) := by
  cases horigin with
  | idx_prefix hprefix hlookup =>
      exact TypeUse.RankedRerollOriginA.idxSuper
        (.idx_prefix hprefix hlookup) htypes hmem
  | idx_current hlo hhi hlookup =>
      exact TypeUse.RankedRerollOriginA.idxSuper
        (.idx_current hlo hhi hlookup) htypes hmem
  | defd_prefix hprefix hlookup =>
      exact TypeUse.RankedRerollOriginA.prefixSuper hprefix hlookup
        hgraph htypes hmem
  | @defd_current i dt hi hlookup =>
      have hcanonical := hgroup i hi
      have hdt : dt = .defd targetRec i :=
        Option.some.inj (hlookup.symm.trans hcanonical)
      subst dt
      cases targetRec with
      | recr targetSts =>
          let sourceRec := unrollRt (.recr targetSts)
          cases hsourceRec : sourceRec with
          | recr sourceSts =>
              have hsourceRecEq :
                  unrollRt (.recr targetSts) = .recr sourceSts := by
                simpa [sourceRec] using hsourceRec
              cases hsourceMember : (SubTypes.toList sourceSts)[i]? with
              | none =>
                  simp [Context.heapSupers, unrollDt, hsourceRecEq,
                    hsourceMember] at hmem
              | some sourceMember =>
                  cases sourceMember with
                  | sub fin sourceSups sourceComp =>
                      have hmem' : g ∈
                          (TypeUses.toList sourceSups).map HeapType.use := by
                        simpa [Context.heapSupers, unrollDt, hsourceRecEq,
                          hsourceMember] using hmem
                      cases hrec with
                      | recr hgroupOrigin =>
                          have hsourceMember' :
                              (SubTypes.toList
                                (match unrollRt (.recr targetSts) with
                                  | .recr sts => sts))[i]? =
                                some (.sub fin sourceSups sourceComp) := by
                            simpa [hsourceRecEq] using hsourceMember
                          obtain ⟨targetSups, targetComp, htargetMember,
                              hsupersOrigin, _⟩ :=
                            hgroupOrigin.getElem_sub hsourceMember'
                          obtain ⟨sourceSuper, hsourceSuper, hg⟩ :=
                            List.mem_map.mp hmem'
                          obtain ⟨j, hsourceGet⟩ :=
                            List.getElem?_of_mem hsourceSuper
                          have hjSource : j <
                              (TypeUses.toList sourceSups).length :=
                            (List.getElem?_eq_some_iff.mp hsourceGet).1
                          have hjTarget : j <
                              (TypeUses.toList targetSups).length := by
                            rw [← hsupersOrigin.length_eq]
                            exact hjSource
                          let targetSuper :=
                            (TypeUses.toList targetSups)[j]'hjTarget
                          have htargetGet :
                              (TypeUses.toList targetSups)[j]? =
                                some targetSuper :=
                            List.getElem?_eq_getElem hjTarget
                          have hordered : TypeUse.RerollBeforeA E base n i
                              sourceSuper targetSuper :=
                            hbefore i (.sub fin sourceSups sourceComp)
                              (.sub fin targetSups targetComp)
                              (by simpa [hsourceRecEq] using hsourceMember)
                              (by simpa using htargetMember)
                              sourceSups targetSups sourceComp targetComp fin
                              rfl rfl j sourceSuper targetSuper
                              hsourceGet htargetGet
                          obtain ⟨s, hslt, hranked⟩ := hordered.ranked
                          exact ⟨sourceSuper, targetSuper, s, hg.symm, hslt,
                            hranked, Heaptype_subA.rec_
                              (by simpa [hrecs] using htargetMember)
                              htargetGet⟩

theorem FieldTypes.RerollOriginA.length_eq
    {E : Context} {base : TypeIdx} {n : Nat}
    {source target : FieldTypes}
    (h : FieldTypes.RerollOriginA E base n source target) :
    (FieldTypes.toList source).length = (FieldTypes.toList target).length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa [FieldTypes.toList] using congrArg Nat.succ ih

theorem FieldTypes.RerollOriginA.getElem
    {E : Context} {base : TypeIdx} {n j : Nat}
    {source target : FieldTypes} {sourceField targetField : FieldType}
    (h : FieldTypes.RerollOriginA E base n source target)
    (hsource : (FieldTypes.toList source)[j]? = some sourceField)
    (htarget : (FieldTypes.toList target)[j]? = some targetField) :
    FieldType.RerollOriginA E base n sourceField targetField := by
  induction h generalizing j sourceField targetField with
  | nil => simp [FieldTypes.toList] at hsource
  | cons hhead htail ih =>
      cases j with
      | zero =>
          simp only [FieldTypes.toList, List.getElem?_cons_zero,
            Option.some.injEq] at hsource htarget
          subst sourceField
          subst targetField
          exact hhead
      | succ j =>
          simp only [FieldTypes.toList, List.getElem?_cons_succ]
            at hsource htarget
          exact ih hsource htarget

theorem ValTypes.RerollOriginA.length_eq
    {E : Context} {base : TypeIdx} {n : Nat}
    {source target : ValTypes}
    (h : ValTypes.RerollOriginA E base n source target) :
    (ValTypes.toList source).length = (ValTypes.toList target).length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa [ValTypes.toList] using congrArg Nat.succ ih

theorem ValTypes.RerollOriginA.getElem
    {E : Context} {base : TypeIdx} {n j : Nat}
    {source target : ValTypes} {sourceType targetType : ValType}
    (h : ValTypes.RerollOriginA E base n source target)
    (hsource : (ValTypes.toList source)[j]? = some sourceType)
    (htarget : (ValTypes.toList target)[j]? = some targetType) :
    ValType.RerollOriginA E base n sourceType targetType := by
  induction h generalizing j sourceType targetType with
  | nil => simp [ValTypes.toList] at hsource
  | cons hhead htail ih =>
      cases j with
      | zero =>
          simp only [ValTypes.toList, List.getElem?_cons_zero,
            Option.some.injEq] at hsource htarget
          subst sourceType
          subst targetType
          exact hhead
      | succ j =>
          simp only [ValTypes.toList, List.getElem?_cons_succ]
            at hsource htarget
          exact ih hsource htarget

private theorem seqAll₂_origin_transport
    {A B A' B' : Type} {OriginA : A → A' → Prop}
    {OriginB : B → B' → Prop} {P : A → B → Prop}
    {Q : A' → B' → Prop}
    {sourceLeft : List A} {targetLeft : List A'}
    {sourceRight : List B} {targetRight : List B'}
    (hlenLeft : sourceLeft.length = targetLeft.length)
    (hlenRight : sourceRight.length = targetRight.length)
    (horiginLeft : ∀ {j : Nat} {source : A} {target : A'},
      sourceLeft[j]? = some source → targetLeft[j]? = some target →
      OriginA source target)
    (horiginRight : ∀ {j : Nat} {source : B} {target : B'},
      sourceRight[j]? = some source → targetRight[j]? = some target →
      OriginB source target)
    (hsource : SeqAll₂ P sourceLeft sourceRight)
    (hmap : ∀ {sourceLeft : A} {targetLeft : A'}
        {sourceRight : B} {targetRight : B'},
      OriginA sourceLeft targetLeft → OriginB sourceRight targetRight →
      P sourceLeft sourceRight → Q targetLeft targetRight) :
    SeqAll₂ Q targetLeft targetRight := by
  intro j targetL targetR htargetL htargetR
  have hjTargetL : j < targetLeft.length :=
    (List.getElem?_eq_some_iff.mp htargetL).1
  have hjTargetR : j < targetRight.length :=
    (List.getElem?_eq_some_iff.mp htargetR).1
  have hjSourceL : j < sourceLeft.length := by omega
  have hjSourceR : j < sourceRight.length := by omega
  let sourceL := sourceLeft[j]'hjSourceL
  let sourceR := sourceRight[j]'hjSourceR
  have hsourceL : sourceLeft[j]? = some sourceL :=
    List.getElem?_eq_getElem hjSourceL
  have hsourceR : sourceRight[j]? = some sourceR :=
    List.getElem?_eq_getElem hjSourceR
  exact hmap (horiginLeft hsourceL htargetL)
    (horiginRight hsourceR htargetR)
    (hsource j sourceL sourceR hsourceL hsourceR)

theorem Type_okA.output_eq_rollDt
    {C : Context} {td : TypeDef} {group : List DefType}
    (h : Type_okA C td group) :
    group = rollDt (TypeIdx.ofNat C.types.length) td.rectype := by
  cases h with
  | @mk base hrange hbase hgroup hrect =>
      have hbaseLt : C.types.length < 2 ^ 32 := by
        unfold TypeGroupRangeOk at hrange
        omega
      have hbaseEq : TypeIdx.ofNat C.types.length = base := by
        apply Subtype.ext
        rw [TypeIdx.ofNat_val_of_lt _ hbaseLt]
        exact hbase.symm
      simpa [hbaseEq] using hgroup

/-- Canonical lookup of the current group's rolled members in any final-vector
extension.  This is the index evidence consumed by `defd_at`; it never infers
an origin from structural equality of defined types. -/
theorem Type_okA.groupLookup_final
    {C : Context} {td : TypeDef} {group tail : List DefType}
    (h : Type_okA C td group) :
    ∀ i : Nat, i < td.rectype.count →
      (C.types ++ group ++ tail)[C.types.length + i]? = some
        (.defd (rollRt (TypeIdx.ofNat C.types.length) td.rectype) i) := by
  have hgroup := h.output_eq_rollDt
  subst group
  intro i hi
  cases td with
  | mk qt =>
      cases qt with
      | recr sts =>
          have hi' : i < SubTypes.length sts := by
            simpa [RecType.count] using hi
          have hgroupLen :
              (rollDt (TypeIdx.ofNat C.types.length) (.recr sts)).length =
                SubTypes.length sts := by
            simp [rollDt, rollRt, SubTypes.length_substSubTypes]
          rw [List.getElem?_append_left (by
            simp only [List.length_append, hgroupLen]
            omega)]
          rw [List.getElem?_append_right (Nat.le_add_right _ _)]
          simp [rollDt, rollRt, SubTypes.length_substSubTypes, hi']

theorem Type_okA.rectypeRollUnrollOrigin_final
    {C : Context} {td : TypeDef} {group tail : List DefType}
    (hsyn : td.isSyn = true) (h : Type_okA C td group) :
    RecType.RerollOriginA
      ({ C with types := C.types ++ group ++ tail } : Context)
      (TypeIdx.ofNat C.types.length) td.rectype.count
      (unrollRt (rollRt (TypeIdx.ofNat C.types.length) td.rectype))
      (rollRt (TypeIdx.ofNat C.types.length) td.rectype) := by
  have hbound : C.types.length + td.rectype.count ≤ 2 ^ 32 := by
    cases h with
    | @mk base hrange hbase hgroup hrect =>
        unfold TypeGroupRangeOk at hrange
        simpa [hbase] using hrange.2
  have hbaseLt : C.types.length < 2 ^ 32 := by
    cases h with
    | @mk base hrange hbase hgroup hrect =>
        exact hrange.1
  have hbound' : (TypeIdx.ofNat C.types.length).val +
      td.rectype.count ≤ 2 ^ 32 := by
    rw [TypeIdx.ofNat_val_of_lt _ hbaseLt]
    exact hbound
  apply RecType.RerollOriginA.rollUnroll
      (E := ({ C with types := C.types ++ group ++ tail } : Context))
      (base := TypeIdx.ofNat C.types.length)
      hbound'
  · intro i hi
    rw [TypeIdx.ofNat_val_of_lt _ hbaseLt]
    exact h.groupLookup_final i hi
  · simpa [TypeDef.isSyn] using hsyn

theorem Type_okA.rectypeRollUnrollBefore_final
    {C : Context} {td : TypeDef} {group tail : List DefType}
    (hsyn : td.isSyn = true) (h : Type_okA C td group) :
    RecType.RerollSupersBeforeA
      ({ C with types := C.types ++ group ++ tail } : Context)
      (TypeIdx.ofNat C.types.length) td.rectype.count
      (unrollRt (rollRt (TypeIdx.ofNat C.types.length) td.rectype))
      (rollRt (TypeIdx.ofNat C.types.length) td.rectype) := by
  cases h with
  | @mk base hrange hbase hgroup hrect =>
      have hbaseLt : C.types.length < 2 ^ 32 := hrange.1
      have hbaseEq : TypeIdx.ofNat C.types.length = base := by
        apply Subtype.ext
        rw [TypeIdx.ofNat_val_of_lt _ hbaseLt]
        exact hbase.symm
      subst base
      apply RecType.RerollSupersBeforeA.rollUnroll
        (B := Context.append C { types := group })
        (tail := tail)
      · simp [Context.append]
      · unfold TypeGroupRangeOk at hrange
        simpa [TypeIdx.ofNat_val_of_lt _ hbaseLt] using hrange.2
      · simpa [TypeDef.isSyn] using hsyn
      · exact hrect
      · intro i hi
        rw [TypeIdx.ofNat_val_of_lt _ hbaseLt]
        have hlookup := Type_okA.groupLookup_final
          (C := C) (td := td) (group := group) (tail := tail)
          (.mk hrange (by
            rw [TypeIdx.ofNat_val_of_lt _ hbaseLt]) hgroup hrect) i hi
        simpa using hlookup

theorem reroll_roll_idx (base x : TypeIdx) (qt : RecType)
    (n : Nat) (hbound : base.val + n ≤ 2 ^ 32) :
    rerollTypeUse base n (rollRt base qt)
        (substTypeUse (.idx x) (rollTVars base n) (rollTUses n)) =
      substTypeUse (.idx x) (rollTVars base n) (rollTUses n) := by
  simp only [substTypeUse, rollTVars, rollTUses]
  rw [substTypeVar_rollVars base x n hbound]
  split <;> simp [rerollTypeUse, *]

theorem reroll_roll_heapType
    {ht : HeapType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ht.isSyn = true) :
    rerollHeapType base n (rollRt base qt)
        (substHeapType ht (rollTVars base n) (rollTUses n)) =
      substHeapType ht (rollTVars base n) (rollTUses n) := by
  cases ht with
  | abs a => rfl
  | use tu =>
      cases tu with
      | idx x =>
          exact congrArg HeapType.use
            (reroll_roll_idx base x qt n hbound)
      | recu i => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | defd dt => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

theorem reroll_roll_refType
    {rt : RefType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : rt.isSyn = true) :
    rerollRefType base n (rollRt base qt)
        (substRefType rt (rollTVars base n) (rollTUses n)) =
      substRefType rt (rollTVars base n) (rollTUses n) := by
  cases rt with
  | ref nul ht =>
      exact congrArg (RefType.ref nul)
        (reroll_roll_heapType base qt n hbound hsyn)

theorem reroll_roll_valType
    {t : ValType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : t.isSyn = true) :
    rerollValType base n (rollRt base qt)
        (substValType t (rollTVars base n) (rollTUses n)) =
      substValType t (rollTVars base n) (rollTUses n) := by
  cases t with
  | num nt => rfl
  | vec vt => rfl
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt =>
      exact congrArg ValType.ref
        (reroll_roll_refType base qt n hbound hsyn)

theorem reroll_roll_storageType
    {zt : StorageType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : zt.isSyn = true) :
    rerollStorageType base n (rollRt base qt)
        (substStorageType zt (rollTVars base n) (rollTUses n)) =
      substStorageType zt (rollTVars base n) (rollTUses n) := by
  cases zt with
  | pack pt => rfl
  | val t =>
      exact congrArg StorageType.val
        (reroll_roll_valType base qt n hbound hsyn)

theorem reroll_roll_fieldType
    {ft : FieldType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ft.isSyn = true) :
    rerollFieldType base n (rollRt base qt)
        (substFieldType ft (rollTVars base n) (rollTUses n)) =
      substFieldType ft (rollTVars base n) (rollTUses n) := by
  cases ft with
  | mk mutability zt =>
      exact congrArg (FieldType.mk mutability)
        (reroll_roll_storageType base qt n hbound hsyn)

private theorem reroll_roll_fieldTypes : ∀ (fts : FieldTypes)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    rerollFieldTypes base n (rollRt base qt)
        (substFieldTypes fts (rollTVars base n) (rollTUses n)) =
      substFieldTypes fts (rollTVars base n) (rollTUses n) := by
  intro fts
  cases fts with
  | nil => intros; rfl
  | cons ft rest =>
      intro base qt n hbound hsyn
      simp only [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substFieldTypes, rerollFieldTypes]
      congr
      · exact reroll_roll_fieldType base qt n hbound hsyn.1
      · exact reroll_roll_fieldTypes rest base qt n hbound hsyn.2

private theorem reroll_roll_valTypes : ∀ (ts : ValTypes)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (ValTypes.toList ts).all ValType.isSyn = true →
    rerollValTypes base n (rollRt base qt)
        (substValTypes ts (rollTVars base n) (rollTUses n)) =
      substValTypes ts (rollTVars base n) (rollTUses n) := by
  intro ts
  cases ts with
  | nil => intros; rfl
  | cons t rest =>
      intro base qt n hbound hsyn
      simp only [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substValTypes, rerollValTypes]
      congr
      · exact reroll_roll_valType base qt n hbound hsyn.1
      · exact reroll_roll_valTypes rest base qt n hbound hsyn.2

theorem reroll_roll_compType
    {ct : CompType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ct.isSyn = true) :
    rerollCompType base n (rollRt base qt)
        (substCompType ct (rollTVars base n) (rollTUses n)) =
      substCompType ct (rollTVars base n) (rollTUses n) := by
  cases ct with
  | struct fields =>
      exact congrArg CompType.struct
        (reroll_roll_fieldTypes fields base qt n hbound hsyn)
  | array field =>
      exact congrArg CompType.array
        (reroll_roll_fieldType base qt n hbound hsyn)
  | func dom cod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      simp only [substCompType, rerollCompType]
      congr
      · exact reroll_roll_valTypes dom base qt n hbound hsyn.1
      · exact reroll_roll_valTypes cod base qt n hbound hsyn.2

private theorem reroll_roll_typeUses : ∀ (sups : TypeUses)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (TypeUses.toList sups).all TypeUse.isSyn = true →
    rerollTypeUses base n (rollRt base qt)
        (substTypeUses sups (rollTVars base n) (rollTUses n)) =
      substTypeUses sups (rollTVars base n) (rollTUses n) := by
  intro sups
  cases sups with
  | nil => intros; rfl
  | cons tu rest =>
      intro base qt n hbound hsyn
      simp only [TypeUses.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substTypeUses, rerollTypeUses]
      congr
      · cases tu with
        | idx x => exact reroll_roll_idx base x qt n hbound
        | recu i => simp [TypeUse.isSyn] at hsyn
        | defd dt => simp [TypeUse.isSyn] at hsyn
      · exact reroll_roll_typeUses rest base qt n hbound hsyn.2

theorem reroll_roll_subType
    {st : SubType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : st.isSyn = true) :
    rerollSubType base n (rollRt base qt)
        (substSubType st (rollTVars base n) (rollTUses n)) =
      substSubType st (rollTVars base n) (rollTUses n) := by
  cases st with
  | sub fin sups ct =>
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      simp only [substSubType, rerollSubType]
      congr
      · exact reroll_roll_typeUses sups base qt n hbound hsyn.1
      · exact reroll_roll_compType base qt n hbound hsyn.2

private theorem reroll_roll_subTypes : ∀ (sts : SubTypes)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (SubTypes.toList sts).all SubType.isSyn = true →
    rerollSubTypes base n (rollRt base qt)
        (substSubTypes sts (rollTVars base n) (rollTUses n)) =
      substSubTypes sts (rollTVars base n) (rollTUses n) := by
  intro sts
  cases sts with
  | nil => intros; rfl
  | cons st rest =>
      intro base qt n hbound hsyn
      simp only [SubTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substSubTypes, rerollSubTypes]
      congr
      · exact reroll_roll_subType base qt n hbound hsyn.1
      · exact reroll_roll_subTypes rest base qt n hbound hsyn.2

theorem reroll_roll_recType
    {qt : RecType} (base : TypeIdx)
    (hbound : base.val + qt.count ≤ 2 ^ 32) (hsyn : qt.isSyn = true) :
    rerollRecType base qt.count (rollRt base qt) (rollRt base qt) =
      rollRt base qt := by
  cases qt with
  | recr sts =>
      simp only [rollRt, rerollRecType]
      exact congrArg RecType.recr
        (reroll_roll_subTypes sts base (.recr sts) (SubTypes.length sts)
          (by simpa [RecType.count] using hbound)
          (by simpa [RecType.isSyn] using hsyn))

theorem reroll_rollUnroll_idx (base x : TypeIdx) (qt : RecType)
    (n : Nat) (hbound : base.val + n ≤ 2 ^ 32) :
    rerollTypeUse base n (rollRt base qt)
        (substTypeUse
          (substTypeUse (.idx x) (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substTypeUse (.idx x) (rollTVars base n) (rollTUses n) := by
  simp only [substTypeUse, rollTVars, rollTUses]
  rw [substTypeVar_rollVars base x n hbound]
  split
  · rename_i hrange
    simp only [substTypeUse, recvTVars, unrollTUses]
    rw [substTypeVar_unrollRecVars]
    have hoff : x.val - base.val < n := by omega
    rw [if_pos hoff]
    simp [rerollTypeUse]
  · rename_i hout
    simp only [substTypeUse, recvTVars, unrollTUses]
    rw [substTypeVar_unrollIdxVars]
    simp [rerollTypeUse, hout]

theorem reroll_rollUnroll_heapType
    {ht : HeapType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ht.isSyn = true) :
    rerollHeapType base n (rollRt base qt)
        (substHeapType
          (substHeapType ht (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substHeapType ht (rollTVars base n) (rollTUses n) := by
  cases ht with
  | abs a => rfl
  | use tu =>
      cases tu with
      | idx x =>
          exact congrArg HeapType.use
            (reroll_rollUnroll_idx base x qt n hbound)
      | recu i => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn
      | defd dt => simp [HeapType.isSyn, TypeUse.isSyn] at hsyn

theorem reroll_rollUnroll_refType
    {rt : RefType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : rt.isSyn = true) :
    rerollRefType base n (rollRt base qt)
        (substRefType
          (substRefType rt (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substRefType rt (rollTVars base n) (rollTUses n) := by
  cases rt with
  | ref nul ht =>
      exact congrArg (RefType.ref nul)
        (reroll_rollUnroll_heapType base qt n hbound hsyn)

theorem reroll_rollUnroll_valType
    {t : ValType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : t.isSyn = true) :
    rerollValType base n (rollRt base qt)
        (substValType
          (substValType t (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substValType t (rollTVars base n) (rollTUses n) := by
  cases t with
  | num nt => rfl
  | vec vt => rfl
  | bot => simp [ValType.isSyn] at hsyn
  | ref rt =>
      exact congrArg ValType.ref
        (reroll_rollUnroll_refType base qt n hbound hsyn)

theorem reroll_rollUnroll_storageType
    {zt : StorageType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : zt.isSyn = true) :
    rerollStorageType base n (rollRt base qt)
        (substStorageType
          (substStorageType zt (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substStorageType zt (rollTVars base n) (rollTUses n) := by
  cases zt with
  | pack pt => rfl
  | val t =>
      exact congrArg StorageType.val
        (reroll_rollUnroll_valType base qt n hbound hsyn)

theorem reroll_rollUnroll_fieldType
    {ft : FieldType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ft.isSyn = true) :
    rerollFieldType base n (rollRt base qt)
        (substFieldType
          (substFieldType ft (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substFieldType ft (rollTVars base n) (rollTUses n) := by
  cases ft with
  | mk mutability zt =>
      exact congrArg (FieldType.mk mutability)
        (reroll_rollUnroll_storageType base qt n hbound hsyn)

private theorem reroll_rollUnroll_fieldTypes : ∀ (fts : FieldTypes)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (FieldTypes.toList fts).all FieldType.isSyn = true →
    rerollFieldTypes base n (rollRt base qt)
        (substFieldTypes
          (substFieldTypes fts (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substFieldTypes fts (rollTVars base n) (rollTUses n) := by
  intro fts
  cases fts with
  | nil => intros; rfl
  | cons ft rest =>
      intro base qt n hbound hsyn
      simp only [FieldTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substFieldTypes, rerollFieldTypes]
      congr
      · exact reroll_rollUnroll_fieldType base qt n hbound hsyn.1
      · exact reroll_rollUnroll_fieldTypes rest base qt n hbound hsyn.2

private theorem reroll_rollUnroll_valTypes : ∀ (ts : ValTypes)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (ValTypes.toList ts).all ValType.isSyn = true →
    rerollValTypes base n (rollRt base qt)
        (substValTypes
          (substValTypes ts (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substValTypes ts (rollTVars base n) (rollTUses n) := by
  intro ts
  cases ts with
  | nil => intros; rfl
  | cons t rest =>
      intro base qt n hbound hsyn
      simp only [ValTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substValTypes, rerollValTypes]
      congr
      · exact reroll_rollUnroll_valType base qt n hbound hsyn.1
      · exact reroll_rollUnroll_valTypes rest base qt n hbound hsyn.2

theorem reroll_rollUnroll_compType
    {ct : CompType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : ct.isSyn = true) :
    rerollCompType base n (rollRt base qt)
        (substCompType
          (substCompType ct (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substCompType ct (rollTVars base n) (rollTUses n) := by
  cases ct with
  | struct fields =>
      exact congrArg CompType.struct
        (reroll_rollUnroll_fieldTypes fields base qt n hbound hsyn)
  | array field =>
      exact congrArg CompType.array
        (reroll_rollUnroll_fieldType base qt n hbound hsyn)
  | func dom cod =>
      rw [CompType.isSyn, Bool.and_eq_true] at hsyn
      simp only [substCompType, rerollCompType]
      congr
      · exact reroll_rollUnroll_valTypes dom base qt n hbound hsyn.1
      · exact reroll_rollUnroll_valTypes cod base qt n hbound hsyn.2

private theorem reroll_rollUnroll_typeUses : ∀ (sups : TypeUses)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (TypeUses.toList sups).all TypeUse.isSyn = true →
    rerollTypeUses base n (rollRt base qt)
        (substTypeUses
          (substTypeUses sups (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substTypeUses sups (rollTVars base n) (rollTUses n) := by
  intro sups
  cases sups with
  | nil => intros; rfl
  | cons tu rest =>
      intro base qt n hbound hsyn
      simp only [TypeUses.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substTypeUses, rerollTypeUses]
      congr
      · cases tu with
        | idx x => exact reroll_rollUnroll_idx base x qt n hbound
        | recu i => simp [TypeUse.isSyn] at hsyn
        | defd dt => simp [TypeUse.isSyn] at hsyn
      · exact reroll_rollUnroll_typeUses rest base qt n hbound hsyn.2

theorem reroll_rollUnroll_subType
    {st : SubType} (base : TypeIdx) (qt : RecType) (n : Nat)
    (hbound : base.val + n ≤ 2 ^ 32) (hsyn : st.isSyn = true) :
    rerollSubType base n (rollRt base qt)
        (substSubType
          (substSubType st (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substSubType st (rollTVars base n) (rollTUses n) := by
  cases st with
  | sub fin sups ct =>
      rw [SubType.isSyn, Bool.and_eq_true] at hsyn
      simp only [substSubType, rerollSubType]
      congr
      · exact reroll_rollUnroll_typeUses sups base qt n hbound hsyn.1
      · exact reroll_rollUnroll_compType base qt n hbound hsyn.2

private theorem reroll_rollUnroll_subTypes : ∀ (sts : SubTypes)
    (base : TypeIdx) (qt : RecType) (n : Nat),
    base.val + n ≤ 2 ^ 32 →
    (SubTypes.toList sts).all SubType.isSyn = true →
    rerollSubTypes base n (rollRt base qt)
        (substSubTypes
          (substSubTypes sts (rollTVars base n) (rollTUses n))
          (recvTVars n) (unrollTUses (rollRt base qt) n)) =
      substSubTypes sts (rollTVars base n) (rollTUses n) := by
  intro sts
  cases sts with
  | nil => intros; rfl
  | cons st rest =>
      intro base qt n hbound hsyn
      simp only [SubTypes.toList, List.all_cons, Bool.and_eq_true] at hsyn
      simp only [substSubTypes, rerollSubTypes]
      congr
      · exact reroll_rollUnroll_subType base qt n hbound hsyn.1
      · exact reroll_rollUnroll_subTypes rest base qt n hbound hsyn.2

theorem rerollReftypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {rolled : RecType}
    {left right : RefType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R (rerollHeapType base n rolled h₁)
        (rerollHeapType base n rolled h₂))
    (h : Reftype_subA E left right) :
    Reftype_subA R (rerollRefType base n rolled left)
      (rerollRefType base n rolled right) := by
  cases h with
  | nonnull hs => exact .nonnull (hheap hs)
  | null hs => exact .null (hheap hs)

theorem rerollValtypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {rolled : RecType}
    {left right : ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R (rerollHeapType base n rolled h₁)
        (rerollHeapType base n rolled h₂))
    (h : Valtype_subA E left right) :
    Valtype_subA R (rerollValType base n rolled left)
      (rerollValType base n rolled right) := by
  cases h with
  | num hs => cases hs; exact .num .mk
  | vec hs => cases hs; exact .vec .mk
  | ref hs => exact .ref (rerollReftypeSubA hheap hs)
  | bot => exact .bot

theorem rerollStoragetypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {rolled : RecType}
    {left right : StorageType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R (rerollHeapType base n rolled h₁)
        (rerollHeapType base n rolled h₂))
    (h : Storagetype_subA E left right) :
    Storagetype_subA R (rerollStorageType base n rolled left)
      (rerollStorageType base n rolled right) := by
  cases h with
  | val hs => exact .val (rerollValtypeSubA hheap hs)
  | pack hs => cases hs; exact .pack .mk

theorem rerollFieldtypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {rolled : RecType}
    {left right : FieldType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R (rerollHeapType base n rolled h₁)
        (rerollHeapType base n rolled h₂))
    (h : Fieldtype_subA E left right) :
    Fieldtype_subA R (rerollFieldType base n rolled left)
      (rerollFieldType base n rolled right) := by
  cases h with
  | const hs => exact .const (rerollStoragetypeSubA hheap hs)
  | var hs₁ hs₂ =>
      simpa [rerollFieldType] using Fieldtype_subA.var
        (rerollStoragetypeSubA hheap hs₁)
        (rerollStoragetypeSubA hheap hs₂)

private theorem rerollResulttypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {rolled : RecType}
    {left right : List ValType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R (rerollHeapType base n rolled h₁)
        (rerollHeapType base n rolled h₂))
    (h : Resulttype_subA E left right) :
    Resulttype_subA R (left.map (rerollValType base n rolled))
      (right.map (rerollValType base n rolled)) := by
  cases h with
  | mk hlen hall =>
      exact Resulttype_subA.mk (by simpa [SeqLen₂] using hlen)
        (seqAll₂_map hlen hall (rerollValtypeSubA hheap))

@[simp] private theorem FieldTypes.toList_reroll
    (fts : FieldTypes) (base : TypeIdx) (n : Nat) (rolled : RecType) :
    FieldTypes.toList (rerollFieldTypes base n rolled fts) =
      (FieldTypes.toList fts).map (rerollFieldType base n rolled) := by
  cases fts with
  | nil => rfl
  | cons ft rest =>
      simp only [rerollFieldTypes, FieldTypes.toList, List.map_cons]
      rw [FieldTypes.toList_reroll]

@[simp] private theorem ValTypes.toList_reroll
    (ts : ValTypes) (base : TypeIdx) (n : Nat) (rolled : RecType) :
    ValTypes.toList (rerollValTypes base n rolled ts) =
      (ValTypes.toList ts).map (rerollValType base n rolled) := by
  cases ts with
  | nil => rfl
  | cons t rest =>
      simp only [rerollValTypes, ValTypes.toList, List.map_cons]
      rw [ValTypes.toList_reroll]

private theorem FieldTypes.reroll_ofList
    (fts : List FieldType) (base : TypeIdx) (n : Nat) (rolled : RecType) :
    rerollFieldTypes base n rolled (FieldTypes.ofList fts) =
      FieldTypes.ofList (fts.map (rerollFieldType base n rolled)) := by
  induction fts with
  | nil => rfl
  | cons ft rest ih =>
      simp only [FieldTypes.ofList, rerollFieldTypes, List.map_cons]
      rw [ih]

theorem rerollComptypeSubA
    {E R : Context} {base : TypeIdx} {n : Nat} {rolled : RecType}
    {left right : CompType}
    (hheap : ∀ {h₁ h₂ : HeapType}, Heaptype_subA E h₁ h₂ →
      Heaptype_subA R (rerollHeapType base n rolled h₁)
        (rerollHeapType base n rolled h₂))
    (h : Comptype_subA E left right) :
    Comptype_subA R (rerollCompType base n rolled left)
      (rerollCompType base n rolled right) := by
  cases h with
  | @struct _ fts₁ extra fts₂ hlen hall =>
      have hfields := seqAll₂_map hlen hall (rerollFieldtypeSubA hheap)
      simp only [rerollCompType, FieldTypes.reroll_ofList, List.map_append]
      exact Comptype_subA.struct (by simpa [SeqLen₂] using hlen) hfields
  | array hs => exact .array (rerollFieldtypeSubA hheap hs)
  | @func _ dom₁ cod₁ dom₂ cod₂ hdom hcod =>
      simp only [rerollCompType]
      apply Comptype_subA.func
      · rw [ValTypes.toList_reroll, ValTypes.toList_reroll]
        exact rerollResulttypeSubA hheap hdom
      · rw [ValTypes.toList_reroll, ValTypes.toList_reroll]
        exact rerollResulttypeSubA hheap hcod

/-! ## Structural transport over proof-indexed origins -/

theorem RefType.RerollOriginA.sub
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : RefType}
    (hleft : RefType.RerollOriginA E base n sourceLeft targetLeft)
    (hright : RefType.RerollOriginA E base n sourceRight targetRight)
    (hheap : ∀ {sourceL targetL sourceR targetR : HeapType},
      HeapType.RerollOriginA E base n sourceL targetL →
      HeapType.RerollOriginA E base n sourceR targetR →
      Heaptype_subA E sourceL sourceR →
      Heaptype_subA R targetL targetR)
    (hsub : Reftype_subA E sourceLeft sourceRight) :
    Reftype_subA R targetLeft targetRight := by
  cases hleft with
  | ref hleft =>
      cases hright with
      | ref hright =>
          cases hsub with
          | nonnull h => exact .nonnull (hheap hleft hright h)
          | null h => exact .null (hheap hleft hright h)

theorem ValType.RerollOriginA.sub
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : ValType}
    (hleft : ValType.RerollOriginA E base n sourceLeft targetLeft)
    (hright : ValType.RerollOriginA E base n sourceRight targetRight)
    (hheap : ∀ {sourceL targetL sourceR targetR : HeapType},
      HeapType.RerollOriginA E base n sourceL targetL →
      HeapType.RerollOriginA E base n sourceR targetR →
      Heaptype_subA E sourceL sourceR →
      Heaptype_subA R targetL targetR)
    (hsub : Valtype_subA E sourceLeft sourceRight) :
    Valtype_subA R targetLeft targetRight := by
  cases hsub with
  | num h =>
      cases hleft with
      | num _ =>
          cases hright with
          | num _ => cases h; exact .num .mk
  | vec h =>
      cases hleft with
      | vec _ =>
          cases hright with
          | vec _ => cases h; exact .vec .mk
  | ref h =>
      cases hleft with
      | ref hleft =>
          cases hright with
          | ref hright =>
              exact .ref (RefType.RerollOriginA.sub
                hleft hright hheap h)
  | bot =>
      cases hleft with
      | bot => exact .bot

theorem StorageType.RerollOriginA.sub
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : StorageType}
    (hleft : StorageType.RerollOriginA E base n sourceLeft targetLeft)
    (hright : StorageType.RerollOriginA E base n sourceRight targetRight)
    (hheap : ∀ {sourceL targetL sourceR targetR : HeapType},
      HeapType.RerollOriginA E base n sourceL targetL →
      HeapType.RerollOriginA E base n sourceR targetR →
      Heaptype_subA E sourceL sourceR →
      Heaptype_subA R targetL targetR)
    (hsub : Storagetype_subA E sourceLeft sourceRight) :
    Storagetype_subA R targetLeft targetRight := by
  cases hsub with
  | pack h =>
      cases hleft with
      | pack _ =>
          cases hright with
          | pack _ => cases h; exact .pack .mk
  | val h =>
      cases hleft with
      | val hleft =>
          cases hright with
          | val hright =>
              exact .val (ValType.RerollOriginA.sub
                hleft hright hheap h)

theorem FieldType.RerollOriginA.sub
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : FieldType}
    (hleft : FieldType.RerollOriginA E base n sourceLeft targetLeft)
    (hright : FieldType.RerollOriginA E base n sourceRight targetRight)
    (hheap : ∀ {sourceL targetL sourceR targetR : HeapType},
      HeapType.RerollOriginA E base n sourceL targetL →
      HeapType.RerollOriginA E base n sourceR targetR →
      Heaptype_subA E sourceL sourceR →
      Heaptype_subA R targetL targetR)
    (hsub : Fieldtype_subA E sourceLeft sourceRight) :
    Fieldtype_subA R targetLeft targetRight := by
  cases hleft with
  | mk hleft =>
      cases hright with
      | mk hright =>
          cases hsub with
          | const h =>
              exact .const (StorageType.RerollOriginA.sub
                hleft hright hheap h)
          | var hforward hbackward =>
              exact .var
                (StorageType.RerollOriginA.sub
                  hleft hright hheap hforward)
                (StorageType.RerollOriginA.sub
                  hright hleft hheap hbackward)

private theorem Resulttype_subA.rerollOrigin
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : ValTypes}
    (hleft : ValTypes.RerollOriginA E base n sourceLeft targetLeft)
    (hright : ValTypes.RerollOriginA E base n sourceRight targetRight)
    (hheap : ∀ {sourceL targetL sourceR targetR : HeapType},
      HeapType.RerollOriginA E base n sourceL targetL →
      HeapType.RerollOriginA E base n sourceR targetR →
      Heaptype_subA E sourceL sourceR →
      Heaptype_subA R targetL targetR)
    (hsub : Resulttype_subA E (ValTypes.toList sourceLeft)
      (ValTypes.toList sourceRight)) :
    Resulttype_subA R (ValTypes.toList targetLeft)
      (ValTypes.toList targetRight) := by
  cases hsub with
  | mk hlen hall =>
      apply Resulttype_subA.mk
      · unfold SeqLen₂ at hlen ⊢
        rw [← hleft.length_eq, ← hright.length_eq]
        exact hlen
      · exact seqAll₂_origin_transport hleft.length_eq hright.length_eq
          (fun hs ht => hleft.getElem hs ht)
          (fun hs ht => hright.getElem hs ht) hall
          (fun hl hr hs => ValType.RerollOriginA.sub hl hr hheap hs)

theorem CompType.RerollOriginA.sub
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : CompType}
    (hleft : CompType.RerollOriginA E base n sourceLeft targetLeft)
    (hright : CompType.RerollOriginA E base n sourceRight targetRight)
    (hheap : ∀ {sourceL targetL sourceR targetR : HeapType},
      HeapType.RerollOriginA E base n sourceL targetL →
      HeapType.RerollOriginA E base n sourceR targetR →
      Heaptype_subA E sourceL sourceR →
      Heaptype_subA R targetL targetR)
    (hsub : Comptype_subA E sourceLeft sourceRight) :
    Comptype_subA R targetLeft targetRight := by
  cases hsub with
  | @struct _ sourcePrefix sourceExtra sourceRight hlen hall =>
      cases hleft with
      | @struct _ targetSourceFields hleft =>
          cases hright with
          | @struct _ targetRightFields hright =>
              let targetFieldsLeft := FieldTypes.toList targetSourceFields
              let targetFieldsRight := FieldTypes.toList targetRightFields
              have htargetRightLeLeft : targetFieldsRight.length ≤
                  targetFieldsLeft.length := by
                have hleftLen := hleft.length_eq
                have hrightLen := hright.length_eq
                unfold targetFieldsLeft targetFieldsRight
                simp only [FieldTypes.toList_ofList] at hleftLen hrightLen
                rw [← hleftLen, ← hrightLen]
                unfold SeqLen₂ at hlen
                simp only [List.length_append]
                omega
              have htargetLen : SeqLen₂
                  (targetFieldsLeft.take targetFieldsRight.length)
                  targetFieldsRight := by
                unfold SeqLen₂
                simp [List.length_take, htargetRightLeLeft]
              have htargetFields : SeqAll₂ (Fieldtype_subA R)
                  (targetFieldsLeft.take targetFieldsRight.length)
                  targetFieldsRight := by
                intro j targetL targetR htargetL htargetR
                have htargetLFull := htargetL
                rw [List.getElem?_take] at htargetLFull
                split at htargetLFull
                · rename_i hjTake
                  have hjRight : j < targetFieldsRight.length :=
                    (List.getElem?_eq_some_iff.mp htargetR).1
                  have hrightLen := hright.length_eq
                  have hjSourceRight : j < sourceRight.length := by
                    unfold targetFieldsRight at hjRight
                    simp only [FieldTypes.toList_ofList] at hrightLen
                    rw [← hrightLen] at hjRight
                    exact hjRight
                  have hjSourcePrefix : j < sourcePrefix.length := by
                    unfold SeqLen₂ at hlen
                    omega
                  let sourceL := sourcePrefix[j]'hjSourcePrefix
                  let sourceR := sourceRight[j]'hjSourceRight
                  have hsourceL : sourcePrefix[j]? = some sourceL :=
                    List.getElem?_eq_getElem hjSourcePrefix
                  have hsourceR : sourceRight[j]? = some sourceR :=
                    List.getElem?_eq_getElem hjSourceRight
                  have hsourceLFull :
                      (FieldTypes.toList (FieldTypes.ofList
                        (sourcePrefix ++ sourceExtra)))[j]? = some sourceL := by
                    simpa [List.getElem?_append_left hjSourcePrefix] using
                      hsourceL
                  have hsourceRFull :
                      (FieldTypes.toList (FieldTypes.ofList sourceRight))[j]? =
                      some sourceR := by
                    simpa using hsourceR
                  exact FieldType.RerollOriginA.sub
                    (hleft.getElem hsourceLFull htargetLFull)
                    (hright.getElem hsourceRFull htargetR) hheap
                    (hall j sourceL sourceR hsourceL hsourceR)
                · simp at htargetLFull
              have hresult := Comptype_subA.struct
                (C := R)
                (fts₁ := targetFieldsLeft.take targetFieldsRight.length)
                (fts₁' := targetFieldsLeft.drop targetFieldsRight.length)
                (fts₂ := targetFieldsRight) htargetLen htargetFields
              simpa [targetFieldsLeft, targetFieldsRight,
                List.take_append_drop, FieldTypes.ofList_toList] using hresult
  | array h =>
      cases hleft with
      | array hleft =>
          cases hright with
          | array hright =>
              exact .array (FieldType.RerollOriginA.sub
                hleft hright hheap h)
  | func hdom hcod =>
      cases hleft with
      | func hleftDom hleftCod =>
          cases hright with
          | func hrightDom hrightCod =>
              exact .func
                (Resulttype_subA.rerollOrigin
                  hrightDom hleftDom hheap hdom)
                (Resulttype_subA.rerollOrigin
                  hleftCod hrightCod hheap hcod)

/-! ## Ranked walk transport with an occurrence-scoped endpoint -/

/-- A heap occurrence with an exact source-vector rank.  Abstract leaves are
unchanged; type-use leaves retain the vector occurrence that selected their
`IDX`, literal `DEF`, or target `REC` presentation. -/
inductive HeapType.RankedRerollOriginA
    (E : Context) (base : TypeIdx) (n : Nat) :
    HeapType → HeapType → Prop where
  | abs (a : AbsHeapType) :
      RankedRerollOriginA E base n (.abs a) (.abs a)
  | use {source target : TypeUse} {r : Nat} :
      TypeUse.RankedRerollOriginA E base n source target r →
      RankedRerollOriginA E base n (.use source) (.use target)

theorem HeapType.RankedRerollOriginA.ok
    {E R : Context} {base : TypeIdx} {n : Nat}
    {source target : HeapType}
    (h : HeapType.RankedRerollOriginA E base n source target)
    (htypes : R.types = E.types) (hrecs : n ≤ R.recs.length)
    (hprefix : ∀ {i : Nat} {dt : DefType}, i < base.val →
      E.types[i]? = some dt → Deftype_okA R dt) :
    Heaptype_okA R target := by
  cases h with
  | abs _ => exact .abs
  | use horigin =>
      apply Heaptype_okA.typeuse
      cases horigin with
      | idx_prefix _ hlookup =>
          exact .typeidx (by simpa [htypes] using hlookup)
      | @idx_current x _ _ _ _ =>
          have hi : x.val - base.val < R.recs.length := by omega
          exact .rec_ (List.getElem?_eq_getElem hi)
      | defd_prefix hlt hlookup =>
          exact .deftype (hprefix hlt hlookup)
      | @defd_current i _ _ _ =>
          have hiR : i < R.recs.length := by omega
          exact .rec_ (List.getElem?_eq_getElem hiR)

/-- Simulate a source declared-super walk in the rerolled recursive scratch
context.  The sole deliberately explicit premise is the zero-step
closure-equivalence case; its proof must retain the two concrete occurrence
origins and cannot be inferred from equal `DefType` terms alone. -/
theorem TypeUse.RankedRerollOriginA.reach
    {E R : Context} {base : TypeIdx} {n r : Nat}
    {source target : TypeUse} {targetRec : RecType}
    (horigin : TypeUse.RankedRerollOriginA E base n source target r)
    (hgraph : E.SourceTypeGraphOkA) (htypes : R.types = E.types)
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd targetRec i))
    (hrec : RecType.RerollOriginA E base n
      (unrollRt targetRec) targetRec)
    (hbefore : RecType.RerollSupersBeforeA E base n
      (unrollRt targetRec) targetRec)
    (hrecs : R.recs = match targetRec with
      | .recr sts => SubTypes.toList sts)
    (hrecsLen : n ≤ R.recs.length)
    (hprefix : ∀ {i : Nat} {dt : DefType}, i < base.val →
      E.types[i]? = some dt → Deftype_okA R dt)
    (hbase : ∀ {sourceLeft targetLeft sourceRight targetRight : TypeUse}
        {leftRank rightRank : Nat},
      TypeUse.RankedRerollOriginA E base n
        sourceLeft targetLeft leftRank →
      TypeUse.RankedRerollOriginA E base n
        sourceRight targetRight rightRank →
      E.heapEq (.use sourceLeft)
        (E.resolveIdx (.use sourceRight)) = true →
      Heaptype_subA R (.use targetLeft) (.use targetRight))
    {sourceRight targetRight : TypeUse} {rightRank fuel : Nat}
    (hright : TypeUse.RankedRerollOriginA E base n
      sourceRight targetRight rightRank)
    (hreach : E.reachDef fuel (.use source)
      (E.resolveIdx (.use sourceRight)) = true) :
    Heaptype_subA R (.use target) (.use targetRight) := by
  let rec go {sourceLeft targetLeft : TypeUse} {leftRank fuel : Nat}
      (hleft : TypeUse.RankedRerollOriginA E base n
        sourceLeft targetLeft leftRank)
      (hreach : E.reachDef fuel (.use sourceLeft)
        (E.resolveIdx (.use sourceRight)) = true) :
      Heaptype_subA R (.use targetLeft) (.use targetRight) := by
    cases fuel with
    | zero =>
        rw [Context.reachDef] at hreach
        exact hbase hleft hright hreach
    | succ fuel =>
        rw [Context.reachDef, Bool.or_eq_true] at hreach
        rcases hreach with heq | hsteps
        · exact hbase hleft hright heq
        · obtain ⟨g, hg, hnextReach⟩ := List.any_eq_true.mp hsteps
          obtain ⟨sourceNext, targetNext, nextRank, rfl, hrank,
              hnext, hstep⟩ := hleft.super hgraph htypes hgroup hrec
                hbefore hrecs hg
          exact Heaptype_subA.trans
            (HeapType.RankedRerollOriginA.ok (.use hnext) htypes
              hrecsLen hprefix)
            hstep (go hnext hnextReach)
  termination_by leftRank
  decreasing_by exact hrank
  exact go horigin hreach

/-- The ranked zero-step case is automatic except when closure-equivalent
defined types cross the prefix/current-group boundary.  Those two cases stay
explicit because discharging them requires the enclosing composite
occurrence; structural equality of the two `DefType` values is insufficient.
Within the current group, canonical vector lookups make the member indices
equal, so the target recursive variables are definitionally reflexive. -/
theorem TypeUse.RankedRerollOriginA.heapEq
    {E R : Context} {base : TypeIdx} {n : Nat}
    {sourceLeft targetLeft sourceRight targetRight : TypeUse}
    {leftRank rightRank : Nat}
    (hleft : TypeUse.RankedRerollOriginA E base n
      sourceLeft targetLeft leftRank)
    (hright : TypeUse.RankedRerollOriginA E base n
      sourceRight targetRight rightRank)
    (htypes : R.types = E.types)
    {targetRec : RecType}
    (hgroup : ∀ i : Nat, i < n →
      E.types[base.val + i]? = some (.defd targetRec i))
    (hprefixCurrent :
      (match targetLeft with | .defd _ => True | _ => False) →
      (match targetRight with | .recu _ => True | _ => False) →
      E.heapEq (.use sourceLeft) (E.resolveIdx (.use sourceRight)) = true →
      Heaptype_subA R (.use targetLeft) (.use targetRight))
    (hcurrentPrefix :
      (match targetLeft with | .recu _ => True | _ => False) →
      (match targetRight with | .idx _ | .defd _ => True | _ => False) →
      E.heapEq (.use sourceLeft) (E.resolveIdx (.use sourceRight)) = true →
      Heaptype_subA R (.use targetLeft) (.use targetRight))
    (heq : E.heapEq (.use sourceLeft)
      (E.resolveIdx (.use sourceRight)) = true) :
    Heaptype_subA R (.use targetLeft) (.use targetRight) := by
  cases hleft with
  | idx_prefix _ _ =>
      cases hright <;>
        simp [Context.heapEq, Context.normHeapType,
          Context.resolveIdx, *] at heq
  | idx_current _ _ _ =>
      cases hright <;>
        simp [Context.heapEq, Context.normHeapType,
          Context.resolveIdx, *] at heq
  | @defd_prefix leftIndex leftDt hlt hlookup =>
      cases hright with
      | @idx_prefix x dt hx hxr =>
          have hclosE : E.closDefType leftDt = E.closDefType dt := by
            simpa [Context.heapEq, Context.normHeapType,
              Context.resolveIdx, hxr] using of_decide_eq_true heq
          have hclos : R.closDefType leftDt = R.closDefType dt := by
            simpa [Context.closDefType, Context.closTypes, htypes] using hclosE
          exact .typeidx_r (by simpa [htypes] using hxr)
            (.def_ (.refl hclos))
      | @defd_prefix i dt hi hir =>
          have hclosE : E.closDefType leftDt = E.closDefType dt := by
            simpa [Context.heapEq, Context.normHeapType,
              Context.resolveIdx] using of_decide_eq_true heq
          have hclos : R.closDefType leftDt = R.closDefType dt := by
            simpa [Context.closDefType, Context.closTypes, htypes] using hclosE
          exact .def_ (.refl hclos)
      | idx_current => exact hprefixCurrent trivial trivial heq
      | defd_current => exact hprefixCurrent trivial trivial heq
  | @defd_current i leftDt hi hlookup =>
      cases hright with
      | idx_prefix => exact hcurrentPrefix trivial trivial heq
      | defd_prefix => exact hcurrentPrefix trivial trivial heq
      | @idx_current x rightDt hlo hhi hrightLookup =>
          have hleftDt : leftDt = .defd targetRec i :=
            Option.some.inj (hlookup.symm.trans (hgroup i hi))
          have hj : x.val - base.val < n := by omega
          have hrightDt : rightDt = .defd targetRec (x.val - base.val) :=
            Option.some.inj (hrightLookup.symm.trans (by
              simpa [Nat.add_sub_of_le hlo] using
                hgroup (x.val - base.val) hj))
          subst leftDt
          subst rightDt
          have hindex : i = x.val - base.val := by
            have hclosed := of_decide_eq_true heq
            simp only [Context.resolveIdx, hrightLookup,
              Context.normHeapType, HeapType.use.injEq,
              TypeUse.defd.injEq] at hclosed
            cases targetRec
            simpa [Context.closDefType, substAllDefType, substDefType] using
              congrArg (fun | .defd _ k => k) hclosed
          subst i
          exact .refl
      | @defd_current j rightDt hj hrightLookup =>
          have hleftDt : leftDt = .defd targetRec i :=
            Option.some.inj (hlookup.symm.trans (hgroup i hi))
          have hrightDt : rightDt = .defd targetRec j :=
            Option.some.inj (hrightLookup.symm.trans (hgroup j hj))
          subst leftDt
          subst rightDt
          have hindex : i = j := by
            have hclosed := of_decide_eq_true heq
            simp only [Context.resolveIdx, Context.normHeapType,
              HeapType.use.injEq, TypeUse.defd.injEq] at hclosed
            cases targetRec
            simpa [Context.closDefType, substAllDefType, substDefType] using
              congrArg (fun | .defd _ k => k) hclosed
          subst j
          exact .refl

end WasmGemmGnaf.Wasm.Core
