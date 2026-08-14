/-
  Wasm/Core/Validation/SubtypingAmended.lean --- the coverage-neutral repair of
  the pinned Core 3.0 bottom-heap subtyping defect, propagated through every
  type validation and subtyping judgment that depends on it.

  The pinned SpecTec source omits `heaptype != BOT` from the `NONE`, `NOFUNC`,
  `NOEXN`, and `NOEXTERN` rules.  Since `BOT <: heaptype` is unconditional,
  those omissions collapse otherwise-disjoint heap hierarchies.  The mutual
  family below repeats the pinned constructors with exactly those four
  premises restored.  Every recursive occurrence is routed through the same
  amended family, including the `Heaptype_ok` premise of transitivity.

  No declaration in this file carries an authority-coverage marker.  Coverage remains
  bound to the unedited pinned transcription in `Validation/Types.lean`; this
  file is an explicit normative amendment, never a replacement authority.
-/
import WasmGemmGnaf.Wasm.Core.Validation.Types

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

mutual

inductive Heaptype_okA : Context → HeapType → Prop where
  | abs {C : Context} {a : AbsHeapType} : Heaptype_okA C (.abs a)
  | typeuse {C : Context} {tu : TypeUse} : Typeuse_okA C tu → Heaptype_okA C (.use tu)

inductive Reftype_okA : Context → RefType → Prop where
  | mk {C : Context} {nul : Option Null} {ht : HeapType} :
      Heaptype_okA C ht → Reftype_okA C (.ref nul ht)

inductive Valtype_okA : Context → ValType → Prop where
  | num {C : Context} {nt : NumType} : Numtype_ok C nt → Valtype_okA C (.num nt)
  | vec {C : Context} {vt : VecType} : Vectype_ok C vt → Valtype_okA C (.vec vt)
  | ref {C : Context} {rt : RefType} : Reftype_okA C rt → Valtype_okA C (.ref rt)
  | bot {C : Context} : Valtype_okA C .bot

inductive Typeuse_okA : Context → TypeUse → Prop where
  | typeidx {C : Context} {x : TypeIdx} {dt : DefType} :
      C.types[x.val]? = some dt → Typeuse_okA C (.idx x)
  | rec_ {C : Context} {i : Nat} {st : SubType} :
      C.recs[i]? = some st → Typeuse_okA C (.recu i)
  | deftype {C : Context} {dt : DefType} : Deftype_okA C dt → Typeuse_okA C (.defd dt)

inductive Resulttype_okA : Context → List ValType → Prop where
  | mk {C : Context} {ts : List ValType} :
      SeqAll (Valtype_okA C) ts → Resulttype_okA C ts

inductive Storagetype_okA : Context → StorageType → Prop where
  | val {C : Context} {t : ValType} : Valtype_okA C t → Storagetype_okA C (.val t)
  | pack {C : Context} {pt : PackType} : Packtype_ok C pt → Storagetype_okA C (.pack pt)

inductive Fieldtype_okA : Context → FieldType → Prop where
  | mk {C : Context} {m : Option Mut} {zt : StorageType} :
      Storagetype_okA C zt → Fieldtype_okA C (.mk m zt)

inductive Comptype_okA : Context → CompType → Prop where
  | struct {C : Context} {fts : FieldTypes} :
      SeqAll (Fieldtype_okA C) (FieldTypes.toList fts) → Comptype_okA C (.struct fts)
  | array {C : Context} {ft : FieldType} :
      Fieldtype_okA C ft → Comptype_okA C (.array ft)
  | func {C : Context} {dom cod : ValTypes} :
      Resulttype_okA C (ValTypes.toList dom) →
      Resulttype_okA C (ValTypes.toList cod) → Comptype_okA C (.func dom cod)

inductive Subtype_okA : Context → SubType → TypeIdx → Prop where
  | mk {C : Context} {fin : Option Final} {xs : List TypeIdx} {ct : CompType}
      {x₀ : TypeIdx} {cts' : List CompType} :
      xs.length ≤ 1 → SeqLen₂ xs cts' →
      SeqAll₂ (fun (x : TypeIdx) (ct' : CompType) =>
          x.val < x₀.val ∧
          ∃ (dt : DefType) (fin' : Option Final) (xs' : List TypeIdx),
            C.types[x.val]? = some dt ∧
            unrollDt dt = some (.sub fin' (TypeUses.ofList (xs'.map TypeUse.idx)) ct'))
        xs cts' →
      Comptype_okA C ct → SeqAll (Comptype_subA C ct) cts' →
      Subtype_okA C (.sub fin (TypeUses.ofList (xs.map TypeUse.idx)) ct) x₀

inductive Subtype_ok2A : Context → SubType → TypeIdx → Nat → Prop where
  | mk {C : Context} {fin : Option Final} {sups : TypeUses} {ct : CompType}
      {x : TypeIdx} {i : Nat} {cts' : List CompType} :
      (TypeUses.toList sups).length ≤ 1 →
      SeqLen₂ (TypeUses.toList sups) cts' →
      SeqAll₂ (fun (tu : TypeUse) (ct' : CompType) =>
          before tu x i = true ∧
          ∃ (fin' : Option Final) (sups' : TypeUses),
            C.unrollHt (.use tu) = some (.sub fin' sups' ct'))
        (TypeUses.toList sups) cts' →
      SeqAll (Typeuse_okA C) (TypeUses.toList sups) →
      Comptype_okA C ct → SeqAll (Comptype_subA C ct) cts' →
      Subtype_ok2A C (.sub fin sups ct) x i

inductive Rectype_okA : Context → RecType → TypeIdx → Prop where
  | empty {C : Context} {x : TypeIdx} : Rectype_okA C (.recr .nil) x
  | cons {C : Context} {st : SubType} {sts : SubTypes} {x : TypeIdx} :
      Subtype_okA C st x → Rectype_okA C (.recr sts) (TypeIdx.ofNat (x.val + 1)) →
      Rectype_okA C (.recr (.cons st sts)) x
  | rec2 {C : Context} {sts : SubTypes} {x : TypeIdx} :
      Rectype_ok2A (C.withRecs (SubTypes.toList sts)) (.recr sts) x 0 →
      Rectype_okA C (.recr sts) x

inductive Rectype_ok2A : Context → RecType → TypeIdx → Nat → Prop where
  | empty {C : Context} {x : TypeIdx} {i : Nat} : Rectype_ok2A C (.recr .nil) x i
  | cons {C : Context} {st : SubType} {sts : SubTypes} {x : TypeIdx} {i : Nat} :
      Subtype_ok2A C st x i →
      Rectype_ok2A C (.recr sts) (TypeIdx.ofNat (x.val + 1)) (i + 1) →
      Rectype_ok2A C (.recr (.cons st sts)) x i

inductive Deftype_okA : Context → DefType → Prop where
  | mk {C : Context} {qt : RecType} {i : Nat} {x : TypeIdx} :
      Rectype_okA C qt x → i < qt.count → Deftype_okA C (.defd qt i)

inductive Heaptype_subA : Context → HeapType → HeapType → Prop where
  | refl {C : Context} {ht : HeapType} : Heaptype_subA C ht ht
  | trans {C : Context} {ht₁ ht₂ ht' : HeapType} :
      Heaptype_okA C ht' → Heaptype_subA C ht₁ ht' → Heaptype_subA C ht' ht₂ →
      Heaptype_subA C ht₁ ht₂
  | eq_any {C : Context} : Heaptype_subA C (.abs .eq) (.abs .any)
  | i31_eq {C : Context} : Heaptype_subA C (.abs .i31) (.abs .eq)
  | struct_eq {C : Context} : Heaptype_subA C (.abs .struct) (.abs .eq)
  | array_eq {C : Context} : Heaptype_subA C (.abs .array) (.abs .eq)
  | struct {C : Context} {dt : DefType} {fts : FieldTypes} :
      Expand dt (.struct fts) → Heaptype_subA C (.use (.defd dt)) (.abs .struct)
  | array {C : Context} {dt : DefType} {ft : FieldType} :
      Expand dt (.array ft) → Heaptype_subA C (.use (.defd dt)) (.abs .array)
  | func {C : Context} {dt : DefType} {dom cod : ValTypes} :
      Expand dt (.func dom cod) → Heaptype_subA C (.use (.defd dt)) (.abs .func)
  | def_ {C : Context} {dt₁ dt₂ : DefType} :
      Deftype_subA C dt₁ dt₂ → Heaptype_subA C (.use (.defd dt₁)) (.use (.defd dt₂))
  | typeidx_l {C : Context} {x : TypeIdx} {dt : DefType} {ht : HeapType} :
      C.types[x.val]? = some dt → Heaptype_subA C (.use (.defd dt)) ht →
      Heaptype_subA C (.use (.idx x)) ht
  | typeidx_r {C : Context} {ht : HeapType} {x : TypeIdx} {dt : DefType} :
      C.types[x.val]? = some dt → Heaptype_subA C ht (.use (.defd dt)) →
      Heaptype_subA C ht (.use (.idx x))
  | rec_ {C : Context} {i j : Nat} {fin : Option Final} {sups : TypeUses}
      {ct : CompType} {tu : TypeUse} :
      C.recs[i]? = some (.sub fin sups ct) →
      (TypeUses.toList sups)[j]? = some tu →
      Heaptype_subA C (.use (.recu i)) (.use tu)
  | none_ {C : Context} {ht : HeapType} :
      ht ≠ .abs .bot → Heaptype_subA C ht (.abs .any) →
      Heaptype_subA C (.abs .none) ht
  | nofunc {C : Context} {ht : HeapType} :
      ht ≠ .abs .bot → Heaptype_subA C ht (.abs .func) →
      Heaptype_subA C (.abs .nofunc) ht
  | noexn {C : Context} {ht : HeapType} :
      ht ≠ .abs .bot → Heaptype_subA C ht (.abs .exn) →
      Heaptype_subA C (.abs .noexn) ht
  | noextern {C : Context} {ht : HeapType} :
      ht ≠ .abs .bot → Heaptype_subA C ht (.abs .extern) →
      Heaptype_subA C (.abs .noextern) ht
  | bot {C : Context} {ht : HeapType} : Heaptype_subA C (.abs .bot) ht

inductive Reftype_subA : Context → RefType → RefType → Prop where
  | nonnull {C : Context} {ht₁ ht₂ : HeapType} :
      Heaptype_subA C ht₁ ht₂ → Reftype_subA C (.ref none ht₁) (.ref none ht₂)
  | null {C : Context} {nul : Option Null} {ht₁ ht₂ : HeapType} :
      Heaptype_subA C ht₁ ht₂ →
      Reftype_subA C (.ref nul ht₁) (.ref (some .null) ht₂)

inductive Valtype_subA : Context → ValType → ValType → Prop where
  | num {C : Context} {nt₁ nt₂ : NumType} :
      Numtype_sub C nt₁ nt₂ → Valtype_subA C (.num nt₁) (.num nt₂)
  | vec {C : Context} {vt₁ vt₂ : VecType} :
      Vectype_sub C vt₁ vt₂ → Valtype_subA C (.vec vt₁) (.vec vt₂)
  | ref {C : Context} {rt₁ rt₂ : RefType} :
      Reftype_subA C rt₁ rt₂ → Valtype_subA C (.ref rt₁) (.ref rt₂)
  | bot {C : Context} {t : ValType} : Valtype_subA C .bot t

inductive Resulttype_subA : Context → List ValType → List ValType → Prop where
  | mk {C : Context} {ts₁ ts₂ : List ValType} :
      SeqLen₂ ts₁ ts₂ → SeqAll₂ (Valtype_subA C) ts₁ ts₂ →
      Resulttype_subA C ts₁ ts₂

inductive Storagetype_subA : Context → StorageType → StorageType → Prop where
  | val {C : Context} {t₁ t₂ : ValType} :
      Valtype_subA C t₁ t₂ → Storagetype_subA C (.val t₁) (.val t₂)
  | pack {C : Context} {pt₁ pt₂ : PackType} :
      Packtype_sub C pt₁ pt₂ → Storagetype_subA C (.pack pt₁) (.pack pt₂)

inductive Fieldtype_subA : Context → FieldType → FieldType → Prop where
  | const {C : Context} {zt₁ zt₂ : StorageType} :
      Storagetype_subA C zt₁ zt₂ → Fieldtype_subA C (.mk none zt₁) (.mk none zt₂)
  | var {C : Context} {zt₁ zt₂ : StorageType} :
      Storagetype_subA C zt₁ zt₂ → Storagetype_subA C zt₂ zt₁ →
      Fieldtype_subA C (.mk (some .mut) zt₁) (.mk (some .mut) zt₂)

inductive Comptype_subA : Context → CompType → CompType → Prop where
  | struct {C : Context} {fts₁ fts₁' fts₂ : List FieldType} :
      SeqLen₂ fts₁ fts₂ → SeqAll₂ (Fieldtype_subA C) fts₁ fts₂ →
      Comptype_subA C (.struct (FieldTypes.ofList (fts₁ ++ fts₁')))
        (.struct (FieldTypes.ofList fts₂))
  | array {C : Context} {ft₁ ft₂ : FieldType} :
      Fieldtype_subA C ft₁ ft₂ → Comptype_subA C (.array ft₁) (.array ft₂)
  | func {C : Context} {dom₁ cod₁ dom₂ cod₂ : ValTypes} :
      Resulttype_subA C (ValTypes.toList dom₂) (ValTypes.toList dom₁) →
      Resulttype_subA C (ValTypes.toList cod₁) (ValTypes.toList cod₂) →
      Comptype_subA C (.func dom₁ cod₁) (.func dom₂ cod₂)

inductive Deftype_subA : Context → DefType → DefType → Prop where
  | refl {C : Context} {dt₁ dt₂ : DefType} :
      C.closDefType dt₁ = C.closDefType dt₂ → Deftype_subA C dt₁ dt₂
  | super {C : Context} {dt₁ dt₂ : DefType} {fin : Option Final} {sups : TypeUses}
      {ct : CompType} {i : Nat} {tu : TypeUse} :
      unrollDt dt₁ = some (.sub fin sups ct) →
      (TypeUses.toList sups)[i]? = some tu →
      Heaptype_subA C (.use tu) (.use (.defd dt₂)) → Deftype_subA C dt₁ dt₂

end

/-! ## Coverage-neutrality for the mutual type family -/

mutual

def Heaptype_okA.to_pinned {C : Context} {ht : HeapType} :
    Heaptype_okA C ht → Heaptype_ok C ht
  | .abs => .abs
  | .typeuse h => .typeuse h.to_pinned

def Reftype_okA.to_pinned {C : Context} {rt : RefType} :
    Reftype_okA C rt → Reftype_ok C rt
  | .mk h => .mk h.to_pinned

def Valtype_okA.to_pinned {C : Context} {t : ValType} :
    Valtype_okA C t → Valtype_ok C t
  | .num h => .num h
  | .vec h => .vec h
  | .ref h => .ref h.to_pinned
  | .bot => .bot

def Typeuse_okA.to_pinned {C : Context} {tu : TypeUse} :
    Typeuse_okA C tu → Typeuse_ok C tu
  | .typeidx h => .typeidx h
  | .rec_ h => .rec_ h
  | .deftype h => .deftype h.to_pinned

def Resulttype_okA.to_pinned {C : Context} {ts : List ValType} :
    Resulttype_okA C ts → Resulttype_ok C ts
  | .mk h => .mk (fun t ht => (h t ht).to_pinned)

def Storagetype_okA.to_pinned {C : Context} {zt : StorageType} :
    Storagetype_okA C zt → Storagetype_ok C zt
  | .val h => .val h.to_pinned
  | .pack h => .pack h

def Fieldtype_okA.to_pinned {C : Context} {ft : FieldType} :
    Fieldtype_okA C ft → Fieldtype_ok C ft
  | .mk h => .mk h.to_pinned

def Comptype_okA.to_pinned {C : Context} {ct : CompType} :
    Comptype_okA C ct → Comptype_ok C ct
  | .struct h => .struct (fun ft hft => (h ft hft).to_pinned)
  | .array h => .array h.to_pinned
  | .func h₁ h₂ => .func h₁.to_pinned h₂.to_pinned

def Subtype_okA.to_pinned {C : Context} {st : SubType} {x : TypeIdx} :
    Subtype_okA C st x → Subtype_ok C st x
  | .mk hlen hlen₂ hbefore hok hsub =>
      .mk hlen hlen₂ hbefore hok.to_pinned (fun ct hct => (hsub ct hct).to_pinned)

def Subtype_ok2A.to_pinned {C : Context} {st : SubType} {x : TypeIdx} {i : Nat} :
    Subtype_ok2A C st x i → Subtype_ok2 C st x i
  | .mk hlen hlen₂ hbefore _ hok hsub =>
      .mk hlen hlen₂ hbefore hok.to_pinned (fun ct hct => (hsub ct hct).to_pinned)

def Rectype_okA.to_pinned {C : Context} {rt : RecType} {x : TypeIdx} :
    Rectype_okA C rt x → Rectype_ok C rt x
  | .empty => .empty
  | .cons h₁ h₂ => .cons h₁.to_pinned h₂.to_pinned
  | .rec2 h => .rec2 h.to_pinned

def Rectype_ok2A.to_pinned {C : Context} {rt : RecType} {x : TypeIdx} {i : Nat} :
    Rectype_ok2A C rt x i → Rectype_ok2 C rt x i
  | .empty => .empty
  | .cons h₁ h₂ => .cons h₁.to_pinned h₂.to_pinned

def Deftype_okA.to_pinned {C : Context} {dt : DefType} :
    Deftype_okA C dt → Deftype_ok C dt
  | .mk h hi => .mk h.to_pinned hi

def Heaptype_subA.to_pinned {C : Context} {ht₁ ht₂ : HeapType} :
    Heaptype_subA C ht₁ ht₂ → Heaptype_sub C ht₁ ht₂
  | .refl => .refl
  | .trans hok h₁ h₂ => .trans hok.to_pinned h₁.to_pinned h₂.to_pinned
  | .eq_any => .eq_any
  | .i31_eq => .i31_eq
  | .struct_eq => .struct_eq
  | .array_eq => .array_eq
  | .struct h => .struct h
  | .array h => .array h
  | .func h => .func h
  | .def_ h => .def_ h.to_pinned
  | .typeidx_l hx h => .typeidx_l hx h.to_pinned
  | .typeidx_r hx h => .typeidx_r hx h.to_pinned
  | .rec_ hr hs => .rec_ hr hs
  | .none_ _ h => .none_ h.to_pinned
  | .nofunc _ h => .nofunc h.to_pinned
  | .noexn _ h => .noexn h.to_pinned
  | .noextern _ h => .noextern h.to_pinned
  | .bot => .bot

def Reftype_subA.to_pinned {C : Context} {rt₁ rt₂ : RefType} :
    Reftype_subA C rt₁ rt₂ → Reftype_sub C rt₁ rt₂
  | .nonnull h => .nonnull h.to_pinned
  | .null h => .null h.to_pinned

def Valtype_subA.to_pinned {C : Context} {t₁ t₂ : ValType} :
    Valtype_subA C t₁ t₂ → Valtype_sub C t₁ t₂
  | .num h => .num h
  | .vec h => .vec h
  | .ref h => .ref h.to_pinned
  | .bot => .bot

def Resulttype_subA.to_pinned {C : Context} {ts₁ ts₂ : List ValType} :
    Resulttype_subA C ts₁ ts₂ → Resulttype_sub C ts₁ ts₂
  | .mk hlen h => .mk hlen (fun i a b ha hb => (h i a b ha hb).to_pinned)

def Storagetype_subA.to_pinned {C : Context} {zt₁ zt₂ : StorageType} :
    Storagetype_subA C zt₁ zt₂ → Storagetype_sub C zt₁ zt₂
  | .val h => .val h.to_pinned
  | .pack h => .pack h

def Fieldtype_subA.to_pinned {C : Context} {ft₁ ft₂ : FieldType} :
    Fieldtype_subA C ft₁ ft₂ → Fieldtype_sub C ft₁ ft₂
  | .const h => .const h.to_pinned
  | .var h₁ h₂ => .var h₁.to_pinned h₂.to_pinned

def Comptype_subA.to_pinned {C : Context} {ct₁ ct₂ : CompType} :
    Comptype_subA C ct₁ ct₂ → Comptype_sub C ct₁ ct₂
  | .struct hlen h =>
      .struct hlen (fun i a b ha hb => (h i a b ha hb).to_pinned)
  | .array h => .array h.to_pinned
  | .func h₁ h₂ => .func h₁.to_pinned h₂.to_pinned

def Deftype_subA.to_pinned {C : Context} {dt₁ dt₂ : DefType} :
    Deftype_subA C dt₁ dt₂ → Deftype_sub C dt₁ dt₂
  | .refl h => .refl h
  | .super hu hi hs => .super hu hi hs.to_pinned

end

inductive Instrtype_okA : Context → InstrType → Prop where
  | mk {C : Context} {it : InstrType} :
      Resulttype_okA C it.dom → Resulttype_okA C it.cod →
      SeqAll (fun (x : LocalIdx) => ∃ lct : LocalType, C.locals[x.val]? = some lct) it.locals →
      Instrtype_okA C it

inductive Instrtype_subA : Context → InstrType → InstrType → Prop where
  | mk {C : Context} {it₁ it₂ : InstrType} :
      Resulttype_subA C it₂.dom it₁.dom → Resulttype_subA C it₁.cod it₂.cod →
      SeqAll (fun (x : LocalIdx) => ∃ t : ValType, C.locals[x.val]? = some ⟨.set, t⟩)
        (setminus it₂.locals it₁.locals) → Instrtype_subA C it₁ it₂

inductive Tagtype_okA : Context → TagType → Prop where
  | mk {C : Context} {jt : TagType} {dom cod : ValTypes} :
      Typeuse_okA C jt → Expand_use C jt (.func dom cod) → Tagtype_okA C jt

inductive Globaltype_okA : Context → GlobalType → Prop where
  | mk {C : Context} {gt : GlobalType} : Valtype_okA C gt.valtype → Globaltype_okA C gt

inductive Tabletype_okA : Context → TableType → Prop where
  | mk {C : Context} {tt : TableType} :
      Limits_ok C tt.lim (2 ^ 32 - 1) → Reftype_okA C tt.elem → Tabletype_okA C tt

inductive Externtype_okA : Context → ExternType → Prop where
  | tag {C : Context} {jt : TagType} : Tagtype_okA C jt → Externtype_okA C (.tag jt)
  | global {C : Context} {gt : GlobalType} : Globaltype_okA C gt → Externtype_okA C (.global gt)
  | mem {C : Context} {mt : MemType} : Memtype_ok C mt → Externtype_okA C (.mem mt)
  | table {C : Context} {tt : TableType} : Tabletype_okA C tt → Externtype_okA C (.table tt)
  | func {C : Context} {tu : TypeUse} {dom cod : ValTypes} :
      Typeuse_okA C tu → Expand_use C tu (.func dom cod) → Externtype_okA C (.func tu)

inductive Tagtype_subA : Context → TagType → TagType → Prop where
  | mk {C : Context} {dt₁ dt₂ : DefType} :
      Deftype_subA C dt₁ dt₂ → Deftype_subA C dt₂ dt₁ →
      Tagtype_subA C (.defd dt₁) (.defd dt₂)

inductive Globaltype_subA : Context → GlobalType → GlobalType → Prop where
  | const {C : Context} {t₁ t₂ : ValType} :
      Valtype_subA C t₁ t₂ → Globaltype_subA C ⟨none, t₁⟩ ⟨none, t₂⟩
  | var {C : Context} {t₁ t₂ : ValType} :
      Valtype_subA C t₁ t₂ → Valtype_subA C t₂ t₁ →
      Globaltype_subA C ⟨some .mut, t₁⟩ ⟨some .mut, t₂⟩

inductive Tabletype_subA : Context → TableType → TableType → Prop where
  | mk {C : Context} {at_ : AddrType} {lim₁ lim₂ : Limits} {rt₁ rt₂ : RefType} :
      Limits_sub C lim₁ lim₂ → Reftype_subA C rt₁ rt₂ → Reftype_subA C rt₂ rt₁ →
      Tabletype_subA C ⟨at_, lim₁, rt₁⟩ ⟨at_, lim₂, rt₂⟩

inductive Externtype_subA : Context → ExternType → ExternType → Prop where
  | tag {C : Context} {jt₁ jt₂ : TagType} :
      Tagtype_subA C jt₁ jt₂ → Externtype_subA C (.tag jt₁) (.tag jt₂)
  | global {C : Context} {gt₁ gt₂ : GlobalType} :
      Globaltype_subA C gt₁ gt₂ → Externtype_subA C (.global gt₁) (.global gt₂)
  | mem {C : Context} {mt₁ mt₂ : MemType} :
      Memtype_sub C mt₁ mt₂ → Externtype_subA C (.mem mt₁) (.mem mt₂)
  | table {C : Context} {tt₁ tt₂ : TableType} :
      Tabletype_subA C tt₁ tt₂ → Externtype_subA C (.table tt₁) (.table tt₂)
  | func {C : Context} {dt₁ dt₂ : DefType} :
      Deftype_subA C dt₁ dt₂ →
      Externtype_subA C (.func (.defd dt₁)) (.func (.defd dt₂))

/-! ## Coverage-neutrality for the non-mutual outer layer -/

def Instrtype_okA.to_pinned {C : Context} {it : InstrType} :
    Instrtype_okA C it → Instrtype_ok C it
  | .mk hdom hcod hloc => .mk hdom.to_pinned hcod.to_pinned hloc

def Instrtype_subA.to_pinned {C : Context} {it₁ it₂ : InstrType} :
    Instrtype_subA C it₁ it₂ → Instrtype_sub C it₁ it₂
  | .mk hdom hcod hloc => .mk hdom.to_pinned hcod.to_pinned hloc

def Tagtype_okA.to_pinned {C : Context} {jt : TagType} :
    Tagtype_okA C jt → Tagtype_ok C jt
  | .mk hok hex => .mk hok.to_pinned hex

def Globaltype_okA.to_pinned {C : Context} {gt : GlobalType} :
    Globaltype_okA C gt → Globaltype_ok C gt
  | .mk h => .mk h.to_pinned

def Tabletype_okA.to_pinned {C : Context} {tt : TableType} :
    Tabletype_okA C tt → Tabletype_ok C tt
  | .mk hl hr => .mk hl hr.to_pinned

def Externtype_okA.to_pinned {C : Context} {xt : ExternType} :
    Externtype_okA C xt → Externtype_ok C xt
  | .tag h => .tag h.to_pinned
  | .global h => .global h.to_pinned
  | .mem h => .mem h
  | .table h => .table h.to_pinned
  | .func hok hex => .func hok.to_pinned hex

def Tagtype_subA.to_pinned {C : Context} {jt₁ jt₂ : TagType} :
    Tagtype_subA C jt₁ jt₂ → Tagtype_sub C jt₁ jt₂
  | .mk h₁ h₂ => .mk h₁.to_pinned h₂.to_pinned

def Globaltype_subA.to_pinned {C : Context} {gt₁ gt₂ : GlobalType} :
    Globaltype_subA C gt₁ gt₂ → Globaltype_sub C gt₁ gt₂
  | .const h => .const h.to_pinned
  | .var h₁ h₂ => .var h₁.to_pinned h₂.to_pinned

def Tabletype_subA.to_pinned {C : Context} {tt₁ tt₂ : TableType} :
    Tabletype_subA C tt₁ tt₂ → Tabletype_sub C tt₁ tt₂
  | .mk hl h₁ h₂ => .mk hl h₁.to_pinned h₂.to_pinned

def Externtype_subA.to_pinned {C : Context} {xt₁ xt₂ : ExternType} :
    Externtype_subA C xt₁ xt₂ → Externtype_sub C xt₁ xt₂
  | .tag h => .tag h.to_pinned
  | .global h => .global h.to_pinned
  | .mem h => .mem h
  | .table h => .table h.to_pinned
  | .func h => .func h.to_pinned

end WasmGemmGnaf.Wasm.Core
