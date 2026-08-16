import WasmGemmGnaf.Wasm.Core.Validation.SubtypingAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-!
  The amended validation and subtyping family depends on a validation context
  only through its `types` and `recs` components.  The executable validator
  changes locals and labels while traversing a body, so its completeness proof
  needs this structural transport rather than a proposition stored in a
  context certificate.
-/

mutual

def Heaptype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {ht : HeapType} :
    Heaptype_okA C ht → Heaptype_okA D ht
  | .abs => .abs
  | .typeuse h => .typeuse (Typeuse_okA.transport htypes hrecs h)

def Reftype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {rt : RefType} :
    Reftype_okA C rt → Reftype_okA D rt
  | .mk h => .mk (Heaptype_okA.transport htypes hrecs h)

def Valtype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {t : ValType} :
    Valtype_okA C t → Valtype_okA D t
  | .num h => by cases h; exact .num .mk
  | .vec h => by cases h; exact .vec .mk
  | .ref h => .ref (Reftype_okA.transport htypes hrecs h)
  | .bot => .bot

def Typeuse_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {tu : TypeUse} :
    Typeuse_okA C tu → Typeuse_okA D tu
  | .typeidx h => .typeidx (by simpa [← htypes] using h)
  | .rec_ h => .rec_ (by simpa [← hrecs] using h)
  | .deftype h => .deftype (Deftype_okA.transport htypes hrecs h)

def Resulttype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {ts : List ValType} :
    Resulttype_okA C ts → Resulttype_okA D ts
  | .mk h => .mk (fun t ht =>
      Valtype_okA.transport htypes hrecs (h t ht))

def Storagetype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {zt : StorageType} :
    Storagetype_okA C zt → Storagetype_okA D zt
  | .val h => .val (Valtype_okA.transport htypes hrecs h)
  | .pack h => by cases h; exact .pack .mk

def Fieldtype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {ft : FieldType} :
    Fieldtype_okA C ft → Fieldtype_okA D ft
  | .mk h => .mk (Storagetype_okA.transport htypes hrecs h)

def Comptype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {ct : CompType} :
    Comptype_okA C ct → Comptype_okA D ct
  | .struct h => .struct (fun ft hft =>
      Fieldtype_okA.transport htypes hrecs (h ft hft))
  | .array h => .array (Fieldtype_okA.transport htypes hrecs h)
  | .func hdom hcod => .func
      (Resulttype_okA.transport htypes hrecs hdom)
      (Resulttype_okA.transport htypes hrecs hcod)

def Subtype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {st : SubType} {x : TypeIdx} :
    Subtype_okA C st x → Subtype_okA D st x
  | .mk hlen hlen₂ hbefore hok hsub => .mk hlen hlen₂
      (fun i idx ct hidxLookup hct => by
        obtain ⟨hidx, dt, fin, xs, hlookup, hunroll⟩ :=
          hbefore i idx ct hidxLookup hct
        exact ⟨hidx, dt, fin, xs, by simpa [← htypes] using hlookup,
          hunroll⟩)
      (Comptype_okA.transport htypes hrecs hok)
      (fun ct hct => Comptype_subA.transport htypes hrecs (hsub ct hct))

def Subtype_ok2A.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {st : SubType} {x : TypeIdx} {i : Nat} :
    Subtype_ok2A C st x i → Subtype_ok2A D st x i
  | .mk hlen hlen₂ hbefore huses hok hsub => .mk hlen hlen₂
      (fun i tu ct htu hct => by
        obtain ⟨hbef, fin, sups, hunroll⟩ := hbefore i tu ct htu hct
        exact ⟨hbef, fin, sups, by
          simpa [Context.unrollHt, ← htypes, ← hrecs] using hunroll⟩)
      (fun tu htu => Typeuse_okA.transport htypes hrecs (huses tu htu))
      (Comptype_okA.transport htypes hrecs hok)
      (fun ct hct => Comptype_subA.transport htypes hrecs (hsub ct hct))

def Rectype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {rt : RecType} {x : TypeIdx} :
    Rectype_okA C rt x → Rectype_okA D rt x
  | .empty => .empty
  | .cons hhead hscope htail => .cons
      (Subtype_okA.transport htypes hrecs hhead) hscope
      (Rectype_okA.transport htypes hrecs htail)
  | .rec2 h => .rec2 (Rectype_ok2A.transport
      (by simpa [Context.withRecs] using htypes)
      (by simp [Context.withRecs]) h)

def Rectype_ok2A.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {rt : RecType} {x : TypeIdx} {i : Nat} :
    Rectype_ok2A C rt x i → Rectype_ok2A D rt x i
  | .empty => .empty
  | .cons hhead htail => .cons
      (Subtype_ok2A.transport htypes hrecs hhead)
      (Rectype_ok2A.transport htypes hrecs htail)

def Deftype_okA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {dt : DefType} :
    Deftype_okA C dt → Deftype_okA D dt
  | .mk h hi => .mk (Rectype_okA.transport htypes hrecs h) hi

def Heaptype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : HeapType} :
    Heaptype_subA C left right → Heaptype_subA D left right
  | .refl => .refl
  | .trans hok hleft hright => .trans
      (Heaptype_okA.transport htypes hrecs hok)
      (Heaptype_subA.transport htypes hrecs hleft)
      (Heaptype_subA.transport htypes hrecs hright)
  | .eq_any => .eq_any
  | .i31_eq => .i31_eq
  | .struct_eq => .struct_eq
  | .array_eq => .array_eq
  | .struct h => .struct h
  | .array h => .array h
  | .func h => .func h
  | .def_ h => .def_ (Deftype_subA.transport htypes hrecs h)
  | .typeidx_l hlookup h => .typeidx_l
      (by simpa [← htypes] using hlookup)
      (Heaptype_subA.transport htypes hrecs h)
  | .typeidx_r hlookup h => .typeidx_r
      (by simpa [← htypes] using hlookup)
      (Heaptype_subA.transport htypes hrecs h)
  | .rec_ hrec hsup => .rec_ (by simpa [← hrecs] using hrec) hsup
  | .rec_struct hrec => .rec_struct (by simpa [← hrecs] using hrec)
  | .rec_array hrec => .rec_array (by simpa [← hrecs] using hrec)
  | .rec_func hrec => .rec_func (by simpa [← hrecs] using hrec)
  | .none_ hne h => .none_ hne (Heaptype_subA.transport htypes hrecs h)
  | .nofunc hne h => .nofunc hne (Heaptype_subA.transport htypes hrecs h)
  | .noexn hne h => .noexn hne (Heaptype_subA.transport htypes hrecs h)
  | .noextern hne h => .noextern hne (Heaptype_subA.transport htypes hrecs h)
  | .bot => .bot

def Reftype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : RefType} :
    Reftype_subA C left right → Reftype_subA D left right
  | .nonnull h => .nonnull (Heaptype_subA.transport htypes hrecs h)
  | .null h => .null (Heaptype_subA.transport htypes hrecs h)

def Valtype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : ValType} :
    Valtype_subA C left right → Valtype_subA D left right
  | .num h => by cases h; exact .num .mk
  | .vec h => by cases h; exact .vec .mk
  | .ref h => .ref (Reftype_subA.transport htypes hrecs h)
  | .bot => .bot

def Resulttype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : List ValType} :
    Resulttype_subA C left right → Resulttype_subA D left right
  | .mk hlen h => .mk hlen (fun i a b ha hb =>
      Valtype_subA.transport htypes hrecs (h i a b ha hb))

def Storagetype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : StorageType} :
    Storagetype_subA C left right → Storagetype_subA D left right
  | .val h => .val (Valtype_subA.transport htypes hrecs h)
  | .pack h => by cases h; exact .pack .mk

def Fieldtype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : FieldType} :
    Fieldtype_subA C left right → Fieldtype_subA D left right
  | .const h => .const (Storagetype_subA.transport htypes hrecs h)
  | .var hleft hright => .var
      (Storagetype_subA.transport htypes hrecs hleft)
      (Storagetype_subA.transport htypes hrecs hright)

def Comptype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : CompType} :
    Comptype_subA C left right → Comptype_subA D left right
  | .struct hlen h => .struct hlen (fun i a b ha hb =>
      Fieldtype_subA.transport htypes hrecs (h i a b ha hb))
  | .array h => .array (Fieldtype_subA.transport htypes hrecs h)
  | .func hdom hcod => .func
      (Resulttype_subA.transport htypes hrecs hdom)
      (Resulttype_subA.transport htypes hrecs hcod)

def Deftype_subA.transport {C D : Context} (htypes : C.types = D.types)
    (hrecs : C.recs = D.recs) {left right : DefType} :
    Deftype_subA C left right → Deftype_subA D left right
  | .refl h => .refl (by
      simpa [Context.closDefType, Context.closTypes, htypes] using h)
  | .super hunroll hlookup h => .super hunroll hlookup
      (Heaptype_subA.transport htypes hrecs h)

end

end WasmGemmGnaf.Wasm.Core
