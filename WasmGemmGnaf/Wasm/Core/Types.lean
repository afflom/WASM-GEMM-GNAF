/-
  Wasm/Core/Types.lean --- the type syntax of the pinned WebAssembly Core 3.0
  front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/1.2-syntax.types.spectec

  at the pinned commit.  Conventions are those fixed in `Core/Values.lean`.

  TWO THINGS THIS FILE HAS TO GET RIGHT, because everything downstream rests on
  them:

  1. THE `/syn` VS `/sem` VARIANT SPLIT.  SpecTec writes three of these
     productions as two fragments of ONE syntactic sort:

         syntax absheaptype/syn = ANY | EQ | ... | NOEXTERN | ...
         syntax absheaptype/sem = ... | BOT
         syntax typeuse/syn = _IDX typeidx | ...
         syntax typeuse/sem = ... | deftype | REC n
         syntax valtype/syn = numtype | vectype | reftype | ...
         syntax valtype/sem = ... | BOT

     There is one sort `absheaptype`, one sort `typeuse`, one sort `valtype`;
     `/syn` and `/sem` name which of its cases a given layer may produce.  The
     transcription therefore declares ONE Lean type per sort carrying ALL the
     cases — `BOT`, `deftype` and `REC n` included, none dropped — together with
     an explicit decidable predicate `isSyn` that recovers the `/syn` fragment.
     `isSyn` is not a convenience: it is the statement of the split, and it is
     what the binary grammar will have to respect, since the binary format can
     only ever produce `/syn` forms.  Splitting into two Lean types instead
     would force `heaptype`, `reftype`, `valtype`, `fieldtype`, `comptype`,
     `subtype`, `rectype` and `deftype` to be duplicated as well, since the
     source gives each of those exactly one definition that mentions both
     fragments.

  2. THE RECURSIVE KNOT.  `deftype` embeds a `rectype`, which lists `subtype`s,
     which list `typeuse`s and carry a `comptype`, which lists `fieldtype`s and
     `resulttype`s, which list `valtype`s, which contain `reftype`s, which
     contain `heaptype`s, which contain `typeuse`s.  All ten sorts are therefore
     one `mutual` block.  Lean forbids a `Subtype` in a nested-inductive
     position, so the `list(...)` sorts inside the knot are companion cons-list
     inductives (`ValTypes`, `TypeUses`, `FieldTypes`, `SubTypes`) and the
     `|X*| < 2^32` bound that `list(...)` imposes is carried by the `wf`
     predicate at the end of the file rather than by the type.  The bound is
     transcribed, not dropped.
-/
import WasmGemmGnaf.Wasm.Core.Values

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-! ## Value types -/

/-- `syntax null = NULL`. -/
-- core-syntax: null
inductive Null where
  | null
  deriving DecidableEq, Repr, Inhabited

/-- `syntax addrtype = I32 | I64`. -/
-- core-syntax: addrtype
inductive AddrType where
  | i32
  | i64
  deriving DecidableEq, Repr, Inhabited

/-- `syntax numtype = I32 | I64 | F32 | F64`. -/
-- core-syntax: numtype
inductive NumType where
  | i32
  | i64
  | f32
  | f64
  deriving DecidableEq, Repr, Inhabited

/-- `syntax vectype = V128`. -/
-- core-syntax: vectype
inductive VecType where
  | v128
  deriving DecidableEq, Repr, Inhabited

/-- `syntax consttype = numtype | vectype`. -/
-- core-syntax: consttype
inductive ConstType where
  | num (nt : NumType)
  | vec (vt : VecType)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax packtype = I8 | I16`. -/
-- core-syntax: packtype
inductive PackType where
  | i8
  | i16
  deriving DecidableEq, Repr, Inhabited

/-- `syntax lanetype = numtype | packtype`. -/
-- core-syntax: lanetype
inductive LaneType where
  | num (nt : NumType)
  | pack (pt : PackType)
  deriving DecidableEq, Repr, Inhabited

/-! ### Sizes

`def $size`, `$vsize`, `$psize`, `$lsize` from the same file. -/

/-- `def $size(numtype) : nat`. -/
def NumType.size : NumType → Nat
  | .i32 => 32
  | .i64 => 64
  | .f32 => 32
  | .f64 => 64

/-- `def $vsize(vectype) : nat`. -/
def VecType.size : VecType → Nat
  | .v128 => 128

/-- `def $psize(packtype) : nat`. -/
def PackType.size : PackType → Nat
  | .i8 => 8
  | .i16 => 16

/-- `def $lsize(lanetype) : nat`. -/
def LaneType.size : LaneType → Nat
  | .num nt => nt.size
  | .pack pt => pt.size

/-- `def $lunpack(lanetype) : numtype`. -/
def LaneType.unpack : LaneType → NumType
  | .num nt => nt
  | .pack _ => .i32

/-! ### Named subfamilies

`Inn`, `Fnn`, `Vnn`, `Cnn`, `Pnn`, `Jnn`, `Lnn` are SpecTec's names for the
subfamilies of `numtype`/`packtype` that index the operator families of
`1.3-syntax.instructions.spectec`. -/

/-- `syntax Inn = I32 | I64`. -/
-- core-syntax: Inn
inductive Inn where
  | i32
  | i64
  deriving DecidableEq, Repr, Inhabited

/-- `syntax Fnn = F32 | F64`. -/
-- core-syntax: Fnn
inductive Fnn where
  | f32
  | f64
  deriving DecidableEq, Repr, Inhabited

/-- `syntax Vnn = V128`. -/
-- core-syntax: Vnn
inductive Vnn where
  | v128
  deriving DecidableEq, Repr, Inhabited

/-- `syntax Cnn = Inn | Fnn | Vnn`. -/
-- core-syntax: Cnn
inductive Cnn where
  | i (n : Inn)
  | f (n : Fnn)
  | v (n : Vnn)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax Pnn = packtype`. -/
-- core-syntax: Pnn
abbrev Pnn : Type := PackType

/-- `syntax Jnn = Inn | Pnn`. -/
-- core-syntax: Jnn
inductive Jnn where
  | i (n : Inn)
  | p (n : Pnn)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax Lnn = Inn | Fnn | Pnn`. -/
-- core-syntax: Lnn
inductive Lnn where
  | i (n : Inn)
  | f (n : Fnn)
  | p (n : Pnn)
  deriving DecidableEq, Repr, Inhabited

namespace Inn

/-- `Inn` as a `numtype`. -/
def toNumType : Inn → NumType
  | .i32 => .i32
  | .i64 => .i64

/-- `def $isize(Inn) : nat`. -/
def size (n : Inn) : Nat := n.toNumType.size

end Inn

namespace Fnn

/-- `Fnn` as a `numtype`. -/
def toNumType : Fnn → NumType
  | .f32 => .f32
  | .f64 => .f64

/-- `def $fsize(Fnn) : nat`. -/
def size (n : Fnn) : Nat := n.toNumType.size

end Fnn

namespace Vnn

/-- `Vnn` as a `vectype`. -/
def toVecType : Vnn → VecType
  | .v128 => .v128

/-- `def $vsize(Vnn) : nat`. -/
def size (n : Vnn) : Nat := n.toVecType.size

end Vnn

namespace Jnn

/-- `Jnn` as a `lanetype`. -/
def toLaneType : Jnn → LaneType
  | .i n => .num n.toNumType
  | .p pt => .pack pt

/-- `def $jsize(Jnn) : nat`. -/
def size (n : Jnn) : Nat := n.toLaneType.size

end Jnn

namespace Lnn

/-- `Lnn` as a `lanetype`. -/
def toLaneType : Lnn → LaneType
  | .i n => .num n.toNumType
  | .f n => .num n.toNumType
  | .p pt => .pack pt

/-- The size of the lane. -/
def size (n : Lnn) : Nat := n.toLaneType.size

end Lnn

namespace Cnn

/-- `Cnn` as a `consttype`. -/
def toConstType : Cnn → ConstType
  | .i n => .num n.toNumType
  | .f n => .num n.toNumType
  | .v n => .vec n.toVecType

end Cnn

namespace NumType

/-- The `Inn` reading of a `numtype`, where there is one. -/
def toInn? : NumType → Option Inn
  | .i32 => some .i32
  | .i64 => some .i64
  | _ => none

/-- The `Fnn` reading of a `numtype`, where there is one. -/
def toFnn? : NumType → Option Fnn
  | .f32 => some .f32
  | .f64 => some .f64
  | _ => none

end NumType

namespace LaneType

/-- The `Jnn` reading of a `lanetype`, where there is one. -/
def toJnn? : LaneType → Option Jnn
  | .num .i32 => some (.i .i32)
  | .num .i64 => some (.i .i64)
  | .num _ => none
  | .pack p => some (.p p)

/-- The `Fnn` reading of a `lanetype`, where there is one. -/
def toFnn? : LaneType → Option Fnn
  | .num .f32 => some .f32
  | .num .f64 => some .f64
  | _ => none

end LaneType

/-! ## Type definitions: the shared vocabulary of the recursive knot -/

/-- `syntax mut = MUT`. -/
-- core-syntax: mut
inductive Mut where
  | mut
  deriving DecidableEq, Repr, Inhabited

/-- `syntax final = FINAL`. -/
-- core-syntax: final
inductive Final where
  | final
  deriving DecidableEq, Repr, Inhabited

/-- `syntax absheaptype/syn = ANY | EQ | I31 | STRUCT | ARRAY | NONE | FUNC
    | NOFUNC | EXN | NOEXN | EXTERN | NOEXTERN | ...` and
`syntax absheaptype/sem = ... | BOT`.

One sort, all cases; `isSyn` recovers the `/syn` fragment.  See the header. -/
-- core-syntax: absheaptype
inductive AbsHeapType where
  | any
  | eq
  | i31
  | struct
  | array
  | none
  | func
  | nofunc
  | exn
  | noexn
  | extern
  | noextern
  | bot
  deriving DecidableEq, Repr, Inhabited

/-- The `absheaptype/syn` fragment: every case except `BOT`. -/
def AbsHeapType.isSyn : AbsHeapType → Bool
  | .bot => false
  | _ => true

/-- `syntax typevar = _IDX typeidx | REC n`. -/
-- core-syntax: typevar
inductive TypeVar where
  | idx (x : TypeIdx)
  | recv (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-! ## The recursive knot

`typeuse`, `heaptype`, `reftype`, `valtype`, `storagetype`, `fieldtype`,
`comptype`, `subtype`, `rectype` and `deftype`, together with the companion
cons-lists that stand for the `list(...)` and `X*` positions inside them. -/

mutual

/-- `syntax typeuse/syn = _IDX typeidx | ...` and
`syntax typeuse/sem = ... | deftype | REC n`.  One sort, all cases. -/
-- core-syntax: typeuse
inductive TypeUse where
  | idx (x : TypeIdx)
  | defd (dt : DefType)
  | recu (n : Nat)

/-- `syntax heaptype = absheaptype | typeuse`. -/
-- core-syntax: heaptype
inductive HeapType where
  | abs (a : AbsHeapType)
  | use (tu : TypeUse)

/-- `syntax reftype = REF null? heaptype`. -/
-- core-syntax: reftype
inductive RefType where
  | ref (nul : Option Null) (ht : HeapType)

/-- `syntax valtype/syn = numtype | vectype | reftype | ...` and
`syntax valtype/sem = ... | BOT`.  One sort, all cases. -/
-- core-syntax: valtype
inductive ValType where
  | num (nt : NumType)
  | vec (vt : VecType)
  | ref (rt : RefType)
  | bot

/-- `syntax storagetype = valtype | packtype`. -/
-- core-syntax: storagetype
inductive StorageType where
  | val (t : ValType)
  | pack (pt : PackType)

/-- `syntax fieldtype = mut? storagetype`. -/
-- core-syntax: fieldtype
inductive FieldType where
  | mk (mutability : Option Mut) (zt : StorageType)

/-- `syntax comptype = STRUCT list(fieldtype) | ARRAY fieldtype
    | FUNC resulttype -> resulttype`. -/
-- core-syntax: comptype
inductive CompType where
  | struct (fts : FieldTypes)
  | array (ft : FieldType)
  | func (dom : ValTypes) (cod : ValTypes)

/-- `syntax subtype = SUB final? typeuse* comptype`. -/
-- core-syntax: subtype
inductive SubType where
  | sub (fin : Option Final) (tus : TypeUses) (ct : CompType)

/-- `syntax rectype = REC list(subtype)`. -/
-- core-syntax: rectype
inductive RecType where
  | recr (sts : SubTypes)

/-- `syntax deftype = _DEF rectype n`. -/
-- core-syntax: deftype
inductive DefType where
  | defd (qt : RecType) (i : Nat)

/-- `valtype*`, as a companion cons-list of the knot. -/
inductive ValTypes where
  | nil
  | cons (t : ValType) (ts : ValTypes)

/-- `typeuse*`, as a companion cons-list of the knot. -/
inductive TypeUses where
  | nil
  | cons (tu : TypeUse) (tus : TypeUses)

/-- `fieldtype*`, as a companion cons-list of the knot. -/
inductive FieldTypes where
  | nil
  | cons (ft : FieldType) (fts : FieldTypes)

/-- `subtype*`, as a companion cons-list of the knot. -/
inductive SubTypes where
  | nil
  | cons (st : SubType) (sts : SubTypes)

end

deriving instance DecidableEq for
  TypeUse, HeapType, RefType, ValType, StorageType, FieldType, CompType,
  SubType, RecType, DefType, ValTypes, TypeUses, FieldTypes, SubTypes

deriving instance Repr for
  TypeUse, HeapType, RefType, ValType, StorageType, FieldType, CompType,
  SubType, RecType, DefType, ValTypes, TypeUses, FieldTypes, SubTypes

instance : Inhabited ValTypes := ⟨.nil⟩
instance : Inhabited TypeUses := ⟨.nil⟩
instance : Inhabited FieldTypes := ⟨.nil⟩
instance : Inhabited ValType := ⟨.bot⟩
instance : Inhabited TypeUse := ⟨.idx default⟩
instance : Inhabited HeapType := ⟨.abs .bot⟩
instance : Inhabited RefType := ⟨.ref none (.abs .bot)⟩
instance : Inhabited StorageType := ⟨.val .bot⟩
instance : Inhabited FieldType := ⟨.mk none (.val .bot)⟩
instance : Inhabited CompType := ⟨.array (.mk none (.val .bot))⟩
instance : Inhabited SubType := ⟨.sub none .nil (.array (.mk none (.val .bot)))⟩
instance : Inhabited SubTypes := ⟨.nil⟩
instance : Inhabited RecType := ⟨.recr .nil⟩
instance : Inhabited DefType := ⟨.defd (.recr .nil) 0⟩

/-- `syntax resulttype = list(valtype)`.

The `|valtype*| < 2^32` bound of `list(...)` is carried by `ValTypes.wfList`
below, because a `Subtype` cannot occur in a nested-inductive position. -/
-- core-syntax: resulttype
abbrev ResultType : Type := ValTypes

/-! ### Cons-list arithmetic on the companions -/

namespace ValTypes

/-- The companion list as an ordinary list. -/
def toList : ValTypes → List ValType
  | .nil => []
  | .cons t ts => t :: toList ts

/-- The companion list of an ordinary list. -/
def ofList : List ValType → ValTypes
  | [] => .nil
  | t :: ts => .cons t (ofList ts)

/-- The number of entries. -/
def length : ValTypes → Nat
  | .nil => 0
  | .cons _ ts => length ts + 1

@[simp] theorem toList_ofList (l : List ValType) : toList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [toList, ofList, ih]

@[simp] theorem ofList_toList : ∀ ts : ValTypes, ofList (toList ts) = ts
  | .nil => rfl
  | .cons t ts => by
      show ValTypes.cons t (ofList (toList ts)) = ValTypes.cons t ts
      rw [ofList_toList ts]

@[simp] theorem length_toList : ∀ ts : ValTypes, (toList ts).length = length ts
  | .nil => rfl
  | .cons _ ts => by
      show (toList ts).length + 1 = length ts + 1
      rw [length_toList ts]

end ValTypes

namespace TypeUses

/-- The companion list as an ordinary list. -/
def toList : TypeUses → List TypeUse
  | .nil => []
  | .cons tu tus => tu :: toList tus

/-- The companion list of an ordinary list. -/
def ofList : List TypeUse → TypeUses
  | [] => .nil
  | tu :: tus => .cons tu (ofList tus)

/-- The number of entries. -/
def length : TypeUses → Nat
  | .nil => 0
  | .cons _ tus => length tus + 1

@[simp] theorem toList_ofList (l : List TypeUse) : toList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons tu tus ih => simp [toList, ofList, ih]

@[simp] theorem ofList_toList : ∀ tus : TypeUses, ofList (toList tus) = tus
  | .nil => rfl
  | .cons tu tus => by
      show TypeUses.cons tu (ofList (toList tus)) = TypeUses.cons tu tus
      rw [ofList_toList tus]

end TypeUses

namespace FieldTypes

/-- The companion list as an ordinary list. -/
def toList : FieldTypes → List FieldType
  | .nil => []
  | .cons ft fts => ft :: toList fts

/-- The companion list of an ordinary list. -/
def ofList : List FieldType → FieldTypes
  | [] => .nil
  | ft :: fts => .cons ft (ofList fts)

/-- The number of entries. -/
def length : FieldTypes → Nat
  | .nil => 0
  | .cons _ fts => length fts + 1

@[simp] theorem toList_ofList (l : List FieldType) : toList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons ft fts ih => simp [toList, ofList, ih]

@[simp] theorem ofList_toList : ∀ fts : FieldTypes, ofList (toList fts) = fts
  | .nil => rfl
  | .cons ft fts => by
      show FieldTypes.cons ft (ofList (toList fts)) = FieldTypes.cons ft fts
      rw [ofList_toList fts]

end FieldTypes

namespace SubTypes

/-- The companion list as an ordinary list. -/
def toList : SubTypes → List SubType
  | .nil => []
  | .cons st sts => st :: toList sts

/-- The companion list of an ordinary list. -/
def ofList : List SubType → SubTypes
  | [] => .nil
  | st :: sts => .cons st (ofList sts)

/-- The number of entries. -/
def length : SubTypes → Nat
  | .nil => 0
  | .cons _ sts => length sts + 1

@[simp] theorem toList_ofList (l : List SubType) : toList (ofList l) = l := by
  induction l with
  | nil => rfl
  | cons st sts ih => simp [toList, ofList, ih]

@[simp] theorem ofList_toList : ∀ sts : SubTypes, ofList (toList sts) = sts
  | .nil => rfl
  | .cons st sts => by
      show SubTypes.cons st (ofList (toList sts)) = SubTypes.cons st sts
      rw [ofList_toList sts]

end SubTypes

/-! ### The `/syn` fragment of the knot

The `/syn` fragment of a compound sort is the fragment reached by taking only
`/syn` cases of the sorts it contains.  This is exactly the fragment the binary
grammar of `5.2-binary.types.spectec` is able to produce. -/

/-- The `typeuse/syn` fragment: `_IDX typeidx` only. -/
def TypeUse.isSyn : TypeUse → Bool
  | .idx _ => true
  | .defd _ => false
  | .recu _ => false

/-- The `/syn` fragment of `heaptype`. -/
def HeapType.isSyn : HeapType → Bool
  | .abs a => a.isSyn
  | .use tu => tu.isSyn

/-- The `/syn` fragment of `reftype`. -/
def RefType.isSyn : RefType → Bool
  | .ref _ ht => ht.isSyn

/-- The `valtype/syn` fragment: `numtype | vectype | reftype`, never `BOT`. -/
def ValType.isSyn : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | .ref rt => rt.isSyn
  | .bot => false

/-- The `/syn` fragment of `storagetype`. -/
def StorageType.isSyn : StorageType → Bool
  | .val t => t.isSyn
  | .pack _ => true

/-- The `/syn` fragment of `fieldtype`. -/
def FieldType.isSyn : FieldType → Bool
  | .mk _ zt => zt.isSyn

/-- The `/syn` fragment of `comptype`.

None of these recurses into a `deftype`: `TypeUse.isSyn` is already `false` on
the `deftype` case, which is precisely the `/sem`-only alternative. -/
def CompType.isSyn : CompType → Bool
  | .struct fts => (FieldTypes.toList fts).all FieldType.isSyn
  | .array ft => ft.isSyn
  | .func dom cod =>
      (ValTypes.toList dom).all ValType.isSyn &&
      (ValTypes.toList cod).all ValType.isSyn

/-- The `/syn` fragment of `subtype`: the declared supertypes are `typeuse`s,
so in the syntax phase each of them is a `_IDX`. -/
def SubType.isSyn : SubType → Bool
  | .sub _ tus ct => (TypeUses.toList tus).all TypeUse.isSyn && ct.isSyn

/-- The `/syn` fragment of `rectype`. -/
def RecType.isSyn : RecType → Bool
  | .recr sts => (SubTypes.toList sts).all SubType.isSyn

/-! ### The `list(...)` bounds inside the knot

`list(X)` carries `|X*| < 2^32`.  Inside the knot that bound cannot live in the
type, so it lives here, checked at every `list(...)` occurrence the source
writes: `rectype = REC list(subtype)`, `comptype = STRUCT list(fieldtype)`, and
the two `resulttype = list(valtype)` positions of `comptype`'s `FUNC`. -/

mutual

/-- Every `list(...)` bound reachable from a `valtype` holds. -/
def ValType.wfList : ValType → Bool
  | .num _ => true
  | .vec _ => true
  | .ref rt => RefType.wfList rt
  | .bot => true

/-- Every `list(...)` bound reachable from a `reftype` holds. -/
def RefType.wfList : RefType → Bool
  | .ref _ ht => HeapType.wfList ht

/-- Every `list(...)` bound reachable from a `heaptype` holds. -/
def HeapType.wfList : HeapType → Bool
  | .abs _ => true
  | .use tu => TypeUse.wfList tu

/-- Every `list(...)` bound reachable from a `typeuse` holds. -/
def TypeUse.wfList : TypeUse → Bool
  | .idx _ => true
  | .defd dt => DefType.wfList dt
  | .recu _ => true

/-- Every `list(...)` bound reachable from a `deftype` holds. -/
def DefType.wfList : DefType → Bool
  | .defd qt _ => RecType.wfList qt

/-- `rectype = REC list(subtype)`: the list bound, plus the bounds below it. -/
def RecType.wfList : RecType → Bool
  | .recr sts => decide (SubTypes.length sts < 2 ^ 32) && SubTypes.wfList sts

/-- Every `list(...)` bound reachable from a `subtype` holds. -/
def SubType.wfList : SubType → Bool
  | .sub _ tus ct => TypeUses.wfList tus && CompType.wfList ct

/-- `comptype`: the `list(fieldtype)` and two `list(valtype)` bounds, plus the
bounds below them. -/
def CompType.wfList : CompType → Bool
  | .struct fts => decide (FieldTypes.length fts < 2 ^ 32) && FieldTypes.wfList fts
  | .array ft => FieldType.wfList ft
  | .func dom cod =>
      decide (ValTypes.length dom < 2 ^ 32) && ValTypes.wfList dom &&
      decide (ValTypes.length cod < 2 ^ 32) && ValTypes.wfList cod

/-- Every `list(...)` bound reachable from a `fieldtype` holds. -/
def FieldType.wfList : FieldType → Bool
  | .mk _ zt => StorageType.wfList zt

/-- Every `list(...)` bound reachable from a `storagetype` holds. -/
def StorageType.wfList : StorageType → Bool
  | .val t => ValType.wfList t
  | .pack _ => true

/-- Every `list(...)` bound reachable from a `valtype*` holds. -/
def ValTypes.wfList : ValTypes → Bool
  | .nil => true
  | .cons t ts => ValType.wfList t && ValTypes.wfList ts

/-- Every `list(...)` bound reachable from a `typeuse*` holds. -/
def TypeUses.wfList : TypeUses → Bool
  | .nil => true
  | .cons tu tus => TypeUse.wfList tu && TypeUses.wfList tus

/-- Every `list(...)` bound reachable from a `fieldtype*` holds. -/
def FieldTypes.wfList : FieldTypes → Bool
  | .nil => true
  | .cons ft fts => FieldType.wfList ft && FieldTypes.wfList fts

/-- Every `list(...)` bound reachable from a `subtype*` holds. -/
def SubTypes.wfList : SubTypes → Bool
  | .nil => true
  | .cons st sts => SubType.wfList st && SubTypes.wfList sts

end

/-! ## External types -/

/-- `syntax limits = `[u64 .. u64?]`. -/
-- core-syntax: limits
structure Limits where
  min : U64
  max : Option U64
  deriving DecidableEq, Repr, Inhabited

/-- `syntax tagtype = typeuse`. -/
-- core-syntax: tagtype
abbrev TagType : Type := TypeUse

/-- `syntax globaltype = mut? valtype`. -/
-- core-syntax: globaltype
structure GlobalType where
  mutability : Option Mut
  valtype : ValType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax memtype = addrtype limits PAGE`.

`PAGE` is a terminal of the production carrying no information — every memory
type is measured in pages — so it contributes no field. -/
-- core-syntax: memtype
structure MemType where
  addr : AddrType
  lim : Limits
  deriving DecidableEq, Repr, Inhabited

/-- `syntax tabletype = addrtype limits reftype`. -/
-- core-syntax: tabletype
structure TableType where
  addr : AddrType
  lim : Limits
  elem : RefType
  deriving DecidableEq, Repr, Inhabited

/-- `syntax datatype = OK`. -/
-- core-syntax: datatype
inductive DataType where
  | ok
  deriving DecidableEq, Repr, Inhabited

/-- `syntax elemtype = reftype`. -/
-- core-syntax: elemtype
abbrev ElemType : Type := RefType

/-- `syntax externtype = TAG tagtype | GLOBAL globaltype | MEM memtype
    | TABLE tabletype | FUNC typeuse`. -/
-- core-syntax: externtype
inductive ExternType where
  | tag (jt : TagType)
  | global (gt : GlobalType)
  | mem (mt : MemType)
  | table (tt : TableType)
  | func (tu : TypeUse)
  deriving DecidableEq, Repr, Inhabited

/-- `syntax moduletype = externtype* -> externtype*`: the imports of a module
mapped to its exports. -/
-- core-syntax: moduletype
structure ModuleType where
  imports : List ExternType
  exports : List ExternType
  deriving DecidableEq, Repr, Inhabited

/-- The `/syn` fragment of `globaltype`. -/
def GlobalType.isSyn (gt : GlobalType) : Bool := gt.valtype.isSyn

/-- The `/syn` fragment of `tabletype`; `memtype` carries no type at all. -/
def TableType.isSyn (tt : TableType) : Bool := tt.elem.isSyn

/-- The `/syn` fragment of `externtype`.  `TAG` and `FUNC` carry a `typeuse`,
which in the syntax phase is a `_IDX`. -/
def ExternType.isSyn : ExternType → Bool
  | .tag jt => jt.isSyn
  | .global gt => gt.isSyn
  | .mem _ => true
  | .table tt => tt.isSyn
  | .func tu => tu.isSyn

namespace ExternType

/-- `def $tagsxt(externtype*) : tagtype*`. -/
def tags : List ExternType → List TagType
  | [] => []
  | .tag jt :: xs => jt :: tags xs
  | _ :: xs => tags xs

/-- `def $globalsxt(externtype*) : globaltype*`. -/
def globals : List ExternType → List GlobalType
  | [] => []
  | .global gt :: xs => gt :: globals xs
  | _ :: xs => globals xs

/-- `def $memsxt(externtype*) : memtype*`. -/
def mems : List ExternType → List MemType
  | [] => []
  | .mem mt :: xs => mt :: mems xs
  | _ :: xs => mems xs

/-- `def $tablesxt(externtype*) : tabletype*`. -/
def tables : List ExternType → List TableType
  | [] => []
  | .table tt :: xs => tt :: tables xs
  | _ :: xs => tables xs

/-- `def $funcsxt(externtype*) : deftype*`, as `typeuse*`; the source coerces
the `FUNC` payload to a `deftype` via `$as_deftype`. -/
def funcs : List ExternType → List TypeUse
  | [] => []
  | .func tu :: xs => tu :: funcs xs
  | _ :: xs => funcs xs

end ExternType

namespace RefType

/-- `def $ANYREF = (REF NULL ANY)`. -/
def anyref : RefType := .ref (some .null) (.abs .any)

/-- `def $EQREF = (REF NULL EQ)`. -/
def eqref : RefType := .ref (some .null) (.abs .eq)

/-- `def $I31REF = (REF NULL I31)`. -/
def i31ref : RefType := .ref (some .null) (.abs .i31)

/-- `def $STRUCTREF = (REF NULL STRUCT)`. -/
def structref : RefType := .ref (some .null) (.abs .struct)

/-- `def $ARRAYREF = (REF NULL ARRAY)`. -/
def arrayref : RefType := .ref (some .null) (.abs .array)

/-- `def $FUNCREF = (REF NULL FUNC)`. -/
def funcref : RefType := .ref (some .null) (.abs .func)

/-- `def $EXNREF = (REF NULL EXN)`. -/
def exnref : RefType := .ref (some .null) (.abs .exn)

/-- `def $EXTERNREF = (REF NULL EXTERN)`. -/
def externref : RefType := .ref (some .null) (.abs .extern)

/-- `def $NULLREF = (REF NULL NONE)`. -/
def nullref : RefType := .ref (some .null) (.abs .none)

/-- `def $NULLFUNCREF = (REF NULL NOFUNC)`. -/
def nullfuncref : RefType := .ref (some .null) (.abs .nofunc)

/-- `def $NULLEXNREF = (REF NULL NOEXN)`. -/
def nullexnref : RefType := .ref (some .null) (.abs .noexn)

/-- `def $NULLEXTERNREF = (REF NULL NOEXTERN)`. -/
def nullexternref : RefType := .ref (some .null) (.abs .noextern)

/-- `def $diffrt(reftype, reftype) : reftype`. -/
def diff : RefType → RefType → RefType
  | .ref _ ht₁, .ref (some .null) _ => .ref none ht₁
  | .ref nul ht₁, .ref none _ => .ref nul ht₁

end RefType

/-- `def $minat(addrtype, addrtype) : addrtype`. -/
def AddrType.min : AddrType → AddrType → AddrType
  | .i32, _ => .i32
  | _, .i32 => .i32
  | .i64, .i64 => .i64

/-- `def $unpack(storagetype) : valtype`. -/
def StorageType.unpack : StorageType → ValType
  | .val t => t
  | .pack _ => .num .i32

end WasmGemmGnaf.Wasm.Core
