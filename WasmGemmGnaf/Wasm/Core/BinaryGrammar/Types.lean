/-
  Wasm/Core/BinaryGrammar/Types.lean --- the DECLARATIVE binary grammar of
  types, for the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every declaration below transcribes a production of

      vendor/wasm-spec/specification/wasm-3.0/5.2-binary.types.spectec

  at the pinned commit.  Conventions are those fixed in
  `BinaryGrammar/Values.lean`; nothing here imports or mentions a decoder.

  THE `/syn` FRAGMENT IS ENFORCED BY CONSTRUCTION, not by an extra predicate.
  `Core/Types.lean` carries `heaptype`, `valtype` and `typeuse` as one Lean type
  each, with an `isSyn` predicate naming the fragment the binary format can
  produce.  The grammar below never mentions `BOT`, a `deftype` or a `REC n`,
  because the pinned productions never do -- so every value it derives is in the
  `/syn` fragment, and that is a fact about the relation rather than a side
  condition bolted onto it.

  THE `Bcomptype` / `Bsubtype` / `Brectype` NEST IS FLAT.  `Bheaptype` reaches a
  type only through `_IDX typeidx`, never through a nested `Bcomptype`, so these
  productions are ordinary non-recursive relations; only `Binstr` is recursive,
  and that knot is tied in `BinaryGrammar/Expressions.lean`.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Values

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

/-! ## Value types -/

/-- `grammar Bnumtype : numtype`. -/
inductive Bnumtype : Bytes → NumType → Prop where
  -- core-opcode: 0x7C F64
  | f64 : Bnumtype [tb 0x7C] .f64
  -- core-opcode: 0x7D F32
  | f32 : Bnumtype [tb 0x7D] .f32
  -- core-opcode: 0x7E I64
  | i64 : Bnumtype [tb 0x7E] .i64
  -- core-opcode: 0x7F I32
  | i32 : Bnumtype [tb 0x7F] .i32

/-- `grammar Bvectype : vectype`. -/
inductive Bvectype : Bytes → VecType → Prop where
  -- core-opcode: 0x7B V128
  | v128 : Bvectype [tb 0x7B] .v128

/-- `grammar Babsheaptype : heaptype`.  The result sort is `heaptype`, as in the
source, not `absheaptype`. -/
inductive Babsheaptype : Bytes → HeapType → Prop where
  -- core-opcode: 0x69 EXN
  | exn : Babsheaptype [tb 0x69] (.abs .exn)
  -- core-opcode: 0x6A ARRAY
  | array : Babsheaptype [tb 0x6A] (.abs .array)
  -- core-opcode: 0x6B STRUCT
  | struct : Babsheaptype [tb 0x6B] (.abs .struct)
  -- core-opcode: 0x6C I31
  | i31 : Babsheaptype [tb 0x6C] (.abs .i31)
  -- core-opcode: 0x6D EQ
  | eq : Babsheaptype [tb 0x6D] (.abs .eq)
  -- core-opcode: 0x6E ANY
  | any : Babsheaptype [tb 0x6E] (.abs .any)
  -- core-opcode: 0x6F EXTERN
  | extern : Babsheaptype [tb 0x6F] (.abs .extern)
  -- core-opcode: 0x70 FUNC
  | func : Babsheaptype [tb 0x70] (.abs .func)
  -- core-opcode: 0x71 NONE
  | none : Babsheaptype [tb 0x71] (.abs .none)
  -- core-opcode: 0x72 NOEXTERN
  | noextern : Babsheaptype [tb 0x72] (.abs .noextern)
  -- core-opcode: 0x73 NOFUNC
  | nofunc : Babsheaptype [tb 0x73] (.abs .nofunc)
  -- core-opcode: 0x74 NOEXN
  | noexn : Babsheaptype [tb 0x74] (.abs .noexn)

/-- `grammar Bheaptype : heaptype`.

The second alternative is `x33:Bs33 => _IDX $s33_to_u32(x33)  -- if x33 >= 0`.
`$s33_to_u32` is declared without equations in `3.1-numerics.scalar.spectec`; on
a non-negative argument the only reading available is the identity on the value,
and requiring the target `typeidx` to exist is exactly SpecTec's demand that the
production be well-typed. -/
inductive Bheaptype : Bytes → HeapType → Prop where
  | abs (bs : Bytes) (ht : HeapType) : Babsheaptype bs ht → Bheaptype bs ht
  | idx (bs : Bytes) (i : Int) (x : TypeIdx) :
      Bs33 bs i → 0 ≤ i → (x.val : Int) = i → Bheaptype bs (.use (.idx x))

/-- `grammar Breftype : reftype`. -/
inductive Breftype : Bytes → RefType → Prop where
  -- core-opcode: 0x63 REF
  | null (bs : Bytes) (ht : HeapType) :
      Bheaptype bs ht → Breftype (tb 0x63 :: bs) (.ref (some .null) ht)
  -- core-opcode: 0x64 REF
  | nonNull (bs : Bytes) (ht : HeapType) :
      Bheaptype bs ht → Breftype (tb 0x64 :: bs) (.ref none ht)
  | abs (bs : Bytes) (ht : HeapType) :
      Babsheaptype bs ht → Breftype bs (.ref (some .null) ht)

/-- `grammar Bvaltype : valtype`. -/
inductive Bvaltype : Bytes → ValType → Prop where
  | num (bs : Bytes) (nt : NumType) : Bnumtype bs nt → Bvaltype bs (.num nt)
  | vec (bs : Bytes) (vt : VecType) : Bvectype bs vt → Bvaltype bs (.vec vt)
  | ref (bs : Bytes) (rt : RefType) : Breftype bs rt → Bvaltype bs (.ref rt)

/-- `grammar Bresulttype : resulttype = | t*:Blist(Bvaltype) => t*`.

`resulttype` is the cons-list companion `ValTypes`; `toList` is the source's
`t*`, and `ValTypes.ofList_toList` in `Core/Types.lean` shows the two views
agree. -/
def Bresulttype (bs : Bytes) (ts : ValTypes) : Prop :=
  Blist Bvaltype bs ts.toList

/-! ## Type definitions -/

/-- `grammar Bmut : mut?`. -/
inductive Bmut : Bytes → Option Mut → Prop where
  -- core-opcode: 0x00 eps
  | const : Bmut [tb 0x00] Option.none
  -- core-opcode: 0x01 MUT
  | mutable : Bmut [tb 0x01] (some Mut.mut)

/-- `grammar Bpacktype : packtype`. -/
inductive Bpacktype : Bytes → PackType → Prop where
  -- core-opcode: 0x77 I16
  | i16 : Bpacktype [tb 0x77] .i16
  -- core-opcode: 0x78 I8
  | i8 : Bpacktype [tb 0x78] .i8

/-- `grammar Bstoragetype : storagetype`. -/
inductive Bstoragetype : Bytes → StorageType → Prop where
  | val (bs : Bytes) (t : ValType) : Bvaltype bs t → Bstoragetype bs (.val t)
  | pack (bs : Bytes) (pt : PackType) : Bpacktype bs pt → Bstoragetype bs (.pack pt)

/-- `grammar Bfieldtype : fieldtype = | zt:Bstoragetype mut?:Bmut => mut? zt`. -/
inductive Bfieldtype : Bytes → FieldType → Prop where
  | mk (bz bm : Bytes) (zt : StorageType) (mo : Option Mut) :
      Bstoragetype bz zt → Bmut bm mo → Bfieldtype (bz ++ bm) (.mk mo zt)

/-- `grammar Bcomptype : comptype`. -/
inductive Bcomptype : Bytes → CompType → Prop where
  -- core-opcode: 0x5E ARRAY
  | array (bs : Bytes) (ft : FieldType) :
      Bfieldtype bs ft → Bcomptype (tb 0x5E :: bs) (.array ft)
  -- core-opcode: 0x5F STRUCT
  | struct (bs : Bytes) (fts : FieldTypes) :
      Blist Bfieldtype bs fts.toList → Bcomptype (tb 0x5F :: bs) (.struct fts)
  -- core-opcode: 0x60 FUNC
  | func (b₁ b₂ : Bytes) (t₁ t₂ : ValTypes) :
      Bresulttype b₁ t₁ → Bresulttype b₂ t₂ →
      Bcomptype (tb 0x60 :: (b₁ ++ b₂)) (.func t₁ t₂)

/-- `grammar Bsubtype : subtype`. -/
inductive Bsubtype : Bytes → SubType → Prop where
  -- core-opcode: 0x4F SUB
  | finalSub (bx bc : Bytes) (xs : List TypeIdx) (tus : TypeUses) (ct : CompType) :
      Blist Btypeidx bx xs → Bcomptype bc ct →
      tus.toList = xs.map TypeUse.idx →
      Bsubtype (tb 0x4F :: (bx ++ bc)) (.sub (some .final) tus ct)
  -- core-opcode: 0x50 SUB
  | openSub (bx bc : Bytes) (xs : List TypeIdx) (tus : TypeUses) (ct : CompType) :
      Blist Btypeidx bx xs → Bcomptype bc ct →
      tus.toList = xs.map TypeUse.idx →
      Bsubtype (tb 0x50 :: (bx ++ bc)) (.sub none tus ct)
  | bare (bc : Bytes) (ct : CompType) :
      Bcomptype bc ct → Bsubtype bc (.sub (some .final) .nil ct)

/-- `grammar Brectype : rectype`. -/
inductive Brectype : Bytes → RecType → Prop where
  -- core-opcode: 0x4E REC
  | recGroup (bs : Bytes) (sts : SubTypes) :
      Blist Bsubtype bs sts.toList → Brectype (tb 0x4E :: bs) (.recr sts)
  | single (bs : Bytes) (st : SubType) :
      Bsubtype bs st → Brectype bs (.recr (.cons st .nil))

/-! ## External types -/

/-- `grammar Blimits : (addrtype, limits)`. -/
inductive Blimits : Bytes → AddrType × Limits → Prop where
  -- core-opcode: 0x00 (I32,
  | i32Min (bs : Bytes) (n : U64) :
      Bu64 bs n → Blimits (tb 0x00 :: bs) (.i32, { min := n, max := none })
  -- core-opcode: 0x01 (I32,
  | i32MinMax (b₁ b₂ : Bytes) (n m : U64) :
      Bu64 b₁ n → Bu64 b₂ m →
      Blimits (tb 0x01 :: (b₁ ++ b₂)) (.i32, { min := n, max := some m })
  -- core-opcode: 0x04 (I64,
  | i64Min (bs : Bytes) (n : U64) :
      Bu64 bs n → Blimits (tb 0x04 :: bs) (.i64, { min := n, max := none })
  -- core-opcode: 0x05 (I64,
  | i64MinMax (b₁ b₂ : Bytes) (n m : U64) :
      Bu64 b₁ n → Bu64 b₂ m →
      Blimits (tb 0x05 :: (b₁ ++ b₂)) (.i64, { min := n, max := some m })

/-- `grammar Btagtype : tagtype = | 0x00 x:Btypeidx => _IDX x`. -/
inductive Btagtype : Bytes → TagType → Prop where
  -- core-opcode: 0x00 _IDX
  | mk (bs : Bytes) (x : TypeIdx) : Btypeidx bs x → Btagtype (tb 0x00 :: bs) (.idx x)

/-- `grammar Bglobaltype : globaltype = | t:Bvaltype mut?:Bmut => mut? t`. -/
inductive Bglobaltype : Bytes → GlobalType → Prop where
  | mk (bt bm : Bytes) (t : ValType) (mo : Option Mut) :
      Bvaltype bt t → Bmut bm mo →
      Bglobaltype (bt ++ bm) { mutability := mo, valtype := t }

/-- `grammar Bmemtype : memtype = | (at,lim):Blimits => at lim PAGE`.

`PAGE` is a terminal carrying no information and `Core/Types.lean` gives it no
field, so the value is determined by the `Blimits` pair alone. -/
inductive Bmemtype : Bytes → MemType → Prop where
  | mk (bs : Bytes) (at' : AddrType) (lim : Limits) :
      Blimits bs (at', lim) → Bmemtype bs { addr := at', lim := lim }

/-- `grammar Btabletype : tabletype = | rt:Breftype (at,lim):Blimits => at lim rt`. -/
inductive Btabletype : Bytes → TableType → Prop where
  | mk (br bl : Bytes) (rt : RefType) (at' : AddrType) (lim : Limits) :
      Breftype br rt → Blimits bl (at', lim) →
      Btabletype (br ++ bl) { addr := at', lim := lim, elem := rt }

/-- `grammar Bexterntype : externtype`.

The five leading bytes coincide with those of `Bexternidx`; `xtask core` takes
the obligation to be the SET of productions, so the two grammars share those
five checklist entries and each is discharged once. -/
inductive Bexterntype : Bytes → ExternType → Prop where
  | func (bs : Bytes) (x : TypeIdx) :
      Btypeidx bs x → Bexterntype (tb 0x00 :: bs) (.func (.idx x))
  | table (bs : Bytes) (tt : TableType) :
      Btabletype bs tt → Bexterntype (tb 0x01 :: bs) (.table tt)
  | mem (bs : Bytes) (mt : MemType) :
      Bmemtype bs mt → Bexterntype (tb 0x02 :: bs) (.mem mt)
  | global (bs : Bytes) (gt : GlobalType) :
      Bglobaltype bs gt → Bexterntype (tb 0x03 :: bs) (.global gt)
  | tag (bs : Bytes) (jt : TagType) :
      Btagtype bs jt → Bexterntype (tb 0x04 :: bs) (.tag jt)

end WasmGemmGnaf.Wasm.Core.Binary
