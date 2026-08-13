/-
  Wasm/Core/Validation/Types.lean --- the declarative validation and subtyping
  judgments on TYPES of the pinned WebAssembly Core 3.0 front end.

  NORMATIVE SOURCE.  Every constructor below transcribes one `rule` of

      vendor/wasm-spec/specification/wasm-3.0/2.1-validation.types.spectec
      vendor/wasm-spec/specification/wasm-3.0/2.2-validation.subtyping.spectec

  at the pinned commit, in source order, one Lean constructor per SpecTec rule,
  carrying that rule's premises as hypotheses and nothing else.

  THE POINT OF THE FILE.  An external audit rejected `validate_iff_declarative`
  because the "declarative" side was the executable checker in disguise, so the
  equivalence was vacuous.  Nothing here imports a checker: the judgments are
  inductive relations read off the pinned rules.  The only functions they call
  are the ones the pinned rules themselves call --- `$unrolldt`, `$expanddt`,
  `$clos_deftype`, `$unrollht`, `$before` --- which are SpecTec `def`s and are
  transcribed in `Core/Subst.lean` and `Core/Context.lean`.  There is
  deliberately no decision procedure in this file and no theorem relating it to
  one.

  WHY ONE `mutual` BLOCK.  `Typeuse_ok` needs `Deftype_ok`, which needs
  `Rectype_ok`, which needs `Subtype_ok`, whose premise `Comptype_sub` is
  subtyping; subtyping's `Heaptype_sub/trans` needs `Heaptype_ok` and
  `Heaptype_sub/def` needs `Deftype_sub`.  Validation and subtyping of types are
  therefore ONE inductive family in Core 3.0 and are transcribed as one.  The
  rules with no premises at all (`Numtype_ok`, `Vectype_ok`, `Packtype_ok` and
  their subtyping counterparts) sit outside the block, as does `Expand`, which
  is an equation on `$expanddt` and recurses into nothing.

  TWO PLACES WHERE THE PINNED SOURCE IS ODD, TRANSCRIBED AS WRITTEN AND FLAGGED
  RATHER THAN QUIETLY REPAIRED:

  * `Subtype_ok` matches its supertype list as `(_IDX x)*` and the unrolled
    supertype as `SUB (_IDX x')* comptype'`, while `Subtype_ok2` --- the
    extended formulation of the same judgment, reached through
    `Rectype_ok/_rec2` --- matches a general `typeuse*`.  The `_IDX` pattern is
    the source's; it is transcribed, not widened.

  * `Limits_sub` matches `` `[n_1 .. m_1] <: `[n_2 .. m_2] `` with no `?` on
    either maximum, although `limits = `[u64 .. u64?]` and `Limits_ok` does
    write `m?`.  As written the rule therefore relates only limits whose maxima
    are both present.  Transcribed as written.
-/
import WasmGemmGnaf.Wasm.Core.Context

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

/-- The number of `subtype`s in a `rectype`, i.e. the `n` of
`rectype = REC subtype^n`. -/
def RecType.count : RecType → Nat
  | .recr sts => SubTypes.length sts

/-! ## Type expansion

`relation Expand: deftype ~~ comptype` and
`relation Expand_use: typeuse ~~_context comptype`. -/

/-- `relation Expand: deftype ~~ comptype`. -/
inductive Expand : DefType → CompType → Prop where
  /-- `rule Expand: deftype ~~ comptype  -- if $expanddt(deftype) = comptype`. -/
  -- core-rule: Expand
  | mk {dt : DefType} {ct : CompType} : expandDt dt = some ct → Expand dt ct

/-- `relation Expand_use: typeuse ~~_context comptype`. -/
inductive Expand_use : Context → TypeUse → CompType → Prop where
  /-- `rule Expand_use/deftype: deftype ~~_C comptype  -- Expand: deftype ~~ comptype`. -/
  -- core-rule: Expand_use/deftype
  | deftype {C : Context} {dt : DefType} {ct : CompType} :
      Expand dt ct → Expand_use C (.defd dt) ct
  /-- `rule Expand_use/typeidx: _IDX typeidx ~~_C comptype
      -- Expand: C.TYPES[typeidx] ~~ comptype`. -/
  -- core-rule: Expand_use/typeidx
  | typeidx {C : Context} {x : TypeIdx} {dt : DefType} {ct : CompType} :
      C.types[x.val]? = some dt → Expand dt ct → Expand_use C (.idx x) ct

/-! ## The premise-free rules

`Numtype_ok`, `Vectype_ok`, `Packtype_ok` and the three reflexivity rules of
`2.2` have no premises, so they are ordinary one-constructor relations. -/

/-- `relation Numtype_ok: context |- numtype : OK`. -/
inductive Numtype_ok : Context → NumType → Prop where
  /-- `rule Numtype_ok: C |- numtype : OK`. -/
  -- core-rule: Numtype_ok
  | mk {C : Context} {nt : NumType} : Numtype_ok C nt

/-- `relation Vectype_ok: context |- vectype : OK`. -/
inductive Vectype_ok : Context → VecType → Prop where
  /-- `rule Vectype_ok: C |- vectype : OK`. -/
  -- core-rule: Vectype_ok
  | mk {C : Context} {vt : VecType} : Vectype_ok C vt

/-- `relation Packtype_ok: context |- packtype : OK`. -/
inductive Packtype_ok : Context → PackType → Prop where
  /-- `rule Packtype_ok: C |- packtype : OK`. -/
  -- core-rule: Packtype_ok
  | mk {C : Context} {pt : PackType} : Packtype_ok C pt

/-- `relation Numtype_sub: context |- numtype <: numtype`. -/
inductive Numtype_sub : Context → NumType → NumType → Prop where
  /-- `rule Numtype_sub: C |- numtype <: numtype`: the SAME `numtype` on both
  sides, so this is equality, not a wildcard pair. -/
  -- core-rule: Numtype_sub
  | mk {C : Context} {nt : NumType} : Numtype_sub C nt nt

/-- `relation Vectype_sub: context |- vectype <: vectype`. -/
inductive Vectype_sub : Context → VecType → VecType → Prop where
  /-- `rule Vectype_sub: C |- vectype <: vectype`. -/
  -- core-rule: Vectype_sub
  | mk {C : Context} {vt : VecType} : Vectype_sub C vt vt

/-- `relation Packtype_sub: context |- packtype <: packtype`. -/
inductive Packtype_sub : Context → PackType → PackType → Prop where
  /-- `rule Packtype_sub: C |- packtype <: packtype`. -/
  -- core-rule: Packtype_sub
  | mk {C : Context} {pt : PackType} : Packtype_sub C pt pt

/-! ## The type judgment

Validation and subtyping of value types, storage types, composite types,
subtypes, recursive types and defined types.  One inductive family; see the
header for why. -/

mutual

/-- `relation Heaptype_ok: context |- heaptype : OK`. -/
inductive Heaptype_ok : Context → HeapType → Prop where
  /-- `rule Heaptype_ok/abs: C |- absheaptype : OK`. -/
  -- core-rule: Heaptype_ok/abs
  | abs {C : Context} {a : AbsHeapType} : Heaptype_ok C (.abs a)
  /-- `rule Heaptype_ok/typeuse: C |- typeuse : OK -- Typeuse_ok: C |- typeuse : OK`. -/
  -- core-rule: Heaptype_ok/typeuse
  | typeuse {C : Context} {tu : TypeUse} : Typeuse_ok C tu → Heaptype_ok C (.use tu)

/-- `relation Reftype_ok: context |- reftype : OK`. -/
inductive Reftype_ok : Context → RefType → Prop where
  /-- `rule Reftype_ok: C |- REF NULL? heaptype : OK -- Heaptype_ok: C |- heaptype : OK`. -/
  -- core-rule: Reftype_ok
  | mk {C : Context} {nul : Option Null} {ht : HeapType} :
      Heaptype_ok C ht → Reftype_ok C (.ref nul ht)

/-- `relation Valtype_ok: context |- valtype : OK`. -/
inductive Valtype_ok : Context → ValType → Prop where
  /-- `rule Valtype_ok/num: C |- numtype : OK -- Numtype_ok: C |- numtype : OK`. -/
  -- core-rule: Valtype_ok/num
  | num {C : Context} {nt : NumType} : Numtype_ok C nt → Valtype_ok C (.num nt)
  /-- `rule Valtype_ok/vec: C |- vectype : OK -- Vectype_ok: C |- vectype : OK`. -/
  -- core-rule: Valtype_ok/vec
  | vec {C : Context} {vt : VecType} : Vectype_ok C vt → Valtype_ok C (.vec vt)
  /-- `rule Valtype_ok/ref: C |- reftype : OK -- Reftype_ok: C |- reftype : OK`. -/
  -- core-rule: Valtype_ok/ref
  | ref {C : Context} {rt : RefType} : Reftype_ok C rt → Valtype_ok C (.ref rt)
  /-- `rule Valtype_ok/bot: C |- BOT : OK`. -/
  -- core-rule: Valtype_ok/bot
  | bot {C : Context} : Valtype_ok C .bot

/-- `relation Typeuse_ok: context |- typeuse : OK`. -/
inductive Typeuse_ok : Context → TypeUse → Prop where
  /-- `rule Typeuse_ok/typeidx: C |- _IDX typeidx : OK -- if C.TYPES[typeidx] = dt`. -/
  -- core-rule: Typeuse_ok/typeidx
  | typeidx {C : Context} {x : TypeIdx} {dt : DefType} :
      C.types[x.val]? = some dt → Typeuse_ok C (.idx x)
  /-- `rule Typeuse_ok/rec: C |- REC i : OK -- if C.RECS[i] = st`. -/
  -- core-rule: Typeuse_ok/rec
  | rec_ {C : Context} {i : Nat} {st : SubType} :
      C.recs[i]? = some st → Typeuse_ok C (.recu i)
  /-- `rule Typeuse_ok/deftype: C |- deftype : OK -- Deftype_ok: C |- deftype : OK`. -/
  -- core-rule: Typeuse_ok/deftype
  | deftype {C : Context} {dt : DefType} : Deftype_ok C dt → Typeuse_ok C (.defd dt)

/-- `relation Resulttype_ok: context |- resulttype : OK`. -/
inductive Resulttype_ok : Context → List ValType → Prop where
  /-- `rule Resulttype_ok: C |- t* : OK -- (Valtype_ok: C |- t : OK)*`. -/
  -- core-rule: Resulttype_ok
  | mk {C : Context} {ts : List ValType} :
      SeqAll (Valtype_ok C) ts → Resulttype_ok C ts

/-- `relation Storagetype_ok: context |- storagetype : OK`. -/
inductive Storagetype_ok : Context → StorageType → Prop where
  /-- `rule Storagetype_ok/val: C |- valtype : OK -- Valtype_ok: C |- valtype : OK`. -/
  -- core-rule: Storagetype_ok/val
  | val {C : Context} {t : ValType} : Valtype_ok C t → Storagetype_ok C (.val t)
  /-- `rule Storagetype_ok/pack: C |- packtype : OK -- Packtype_ok: C |- packtype : OK`. -/
  -- core-rule: Storagetype_ok/pack
  | pack {C : Context} {pt : PackType} : Packtype_ok C pt → Storagetype_ok C (.pack pt)

/-- `relation Fieldtype_ok: context |- fieldtype : OK`. -/
inductive Fieldtype_ok : Context → FieldType → Prop where
  /-- `rule Fieldtype_ok: C |- MUT? storagetype : OK
      -- Storagetype_ok: C |- storagetype : OK`. -/
  -- core-rule: Fieldtype_ok
  | mk {C : Context} {m : Option Mut} {zt : StorageType} :
      Storagetype_ok C zt → Fieldtype_ok C (.mk m zt)

/-- `relation Comptype_ok: context |- comptype : OK`. -/
inductive Comptype_ok : Context → CompType → Prop where
  /-- `rule Comptype_ok/struct: C |- STRUCT fieldtype* : OK
      -- (Fieldtype_ok: C |- fieldtype : OK)*`. -/
  -- core-rule: Comptype_ok/struct
  | struct {C : Context} {fts : FieldTypes} :
      SeqAll (Fieldtype_ok C) (FieldTypes.toList fts) → Comptype_ok C (.struct fts)
  /-- `rule Comptype_ok/array: C |- ARRAY fieldtype : OK
      -- Fieldtype_ok: C |- fieldtype : OK`. -/
  -- core-rule: Comptype_ok/array
  | array {C : Context} {ft : FieldType} : Fieldtype_ok C ft → Comptype_ok C (.array ft)
  /-- `rule Comptype_ok/func: C |- FUNC t_1* -> t_2* : OK
      -- Resulttype_ok: C |- t_1* : OK -- Resulttype_ok: C |- t_2* : OK`. -/
  -- core-rule: Comptype_ok/func
  | func {C : Context} {dom cod : ValTypes} :
      Resulttype_ok C (ValTypes.toList dom) → Resulttype_ok C (ValTypes.toList cod) →
      Comptype_ok C (.func dom cod)

/-- `relation Subtype_ok: context |- subtype : oktypeidx`. -/
inductive Subtype_ok : Context → SubType → TypeIdx → Prop where
  /-- `rule Subtype_ok:
        C |- SUB FINAL? (_IDX x)* comptype : OK(x_0)
        -- if |x*| <= 1
        -- (if x < x_0)*
        -- (if $unrolldt(C.TYPES[x]) = SUB (_IDX x')* comptype')*
        -- Comptype_ok: C |- comptype : OK
        -- (Comptype_sub: C |- comptype <: comptype')*`

  `cts'` is the sequence of `comptype'`, one per declared supertype index. -/
  -- core-rule: Subtype_ok
  | mk {C : Context} {fin : Option Final} {xs : List TypeIdx} {ct : CompType}
      {x₀ : TypeIdx} {cts' : List CompType} :
      xs.length ≤ 1 →
      SeqLen₂ xs cts' →
      SeqAll₂ (fun (x : TypeIdx) (ct' : CompType) =>
          x.val < x₀.val ∧
          ∃ (dt : DefType) (fin' : Option Final) (xs' : List TypeIdx),
            C.types[x.val]? = some dt ∧
            unrollDt dt = some (.sub fin' (TypeUses.ofList (xs'.map TypeUse.idx)) ct'))
        xs cts' →
      Comptype_ok C ct →
      SeqAll (Comptype_sub C ct) cts' →
      Subtype_ok C (.sub fin (TypeUses.ofList (xs.map TypeUse.idx)) ct) x₀

/-- `relation Subtype_ok2: context |- subtype : oktypeidxnat`. -/
inductive Subtype_ok2 : Context → SubType → TypeIdx → Nat → Prop where
  /-- `rule Subtype_ok2:
        C |- SUB FINAL? typeuse* compttype : OK x i
        -- if |typeuse*| <= 1
        -- (if $before(typeuse, x, i))*
        -- (if $unrollht(C, typeuse) = SUB typeuse'* comptype')*
        -- Comptype_ok: C |- comptype : OK
        -- (Comptype_sub: C |- comptype <: comptype')*`

  The pinned source spells the conclusion's composite type `compttype` and its
  premises' `comptype`; there is no other composite type in the rule, so the two
  are the same variable and the extra `t` is a typo in the source.  Transcribed
  as one variable. -/
  -- core-rule: Subtype_ok2
  | mk {C : Context} {fin : Option Final} {sups : TypeUses} {ct : CompType}
      {x : TypeIdx} {i : Nat} {cts' : List CompType} :
      (TypeUses.toList sups).length ≤ 1 →
      SeqLen₂ (TypeUses.toList sups) cts' →
      SeqAll₂ (fun (tu : TypeUse) (ct' : CompType) =>
          before tu x i = true ∧
          ∃ (fin' : Option Final) (sups' : TypeUses),
            C.unrollHt (.use tu) = some (.sub fin' sups' ct'))
        (TypeUses.toList sups) cts' →
      Comptype_ok C ct →
      SeqAll (Comptype_sub C ct) cts' →
      Subtype_ok2 C (.sub fin sups ct) x i

/-- `relation Rectype_ok: context |- rectype : oktypeidx`. -/
inductive Rectype_ok : Context → RecType → TypeIdx → Prop where
  /-- `rule Rectype_ok/empty: C |- REC eps : OK(x)`. -/
  -- core-rule: Rectype_ok/empty
  | empty {C : Context} {x : TypeIdx} : Rectype_ok C (.recr .nil) x
  /-- `rule Rectype_ok/cons:
        C |- REC (subtype_1 subtype*) : OK(x)
        -- Subtype_ok: C |- subtype_1 : OK(x)
        -- Rectype_ok: C |- REC subtype* : OK($(x+1))`. -/
  -- core-rule: Rectype_ok/cons
  | cons {C : Context} {st : SubType} {sts : SubTypes} {x : TypeIdx} :
      Subtype_ok C st x →
      Rectype_ok C (.recr sts) (TypeIdx.ofNat (x.val + 1)) →
      Rectype_ok C (.recr (.cons st sts)) x
  /-- `rule Rectype_ok/_rec2:
        C |- REC subtype* : OK(x)
        -- Rectype_ok2: C, RECS subtype* |- REC subtype* : OK x 0`. -/
  -- core-rule: Rectype_ok/_rec2
  | rec2 {C : Context} {sts : SubTypes} {x : TypeIdx} :
      Rectype_ok2 (C.withRecs (SubTypes.toList sts)) (.recr sts) x 0 →
      Rectype_ok C (.recr sts) x

/-- `relation Rectype_ok2: context |- rectype : oktypeidxnat`. -/
inductive Rectype_ok2 : Context → RecType → TypeIdx → Nat → Prop where
  /-- `rule Rectype_ok2/empty: C |- REC eps : OK x i`. -/
  -- core-rule: Rectype_ok2/empty
  | empty {C : Context} {x : TypeIdx} {i : Nat} : Rectype_ok2 C (.recr .nil) x i
  /-- `rule Rectype_ok2/cons:
        C |- REC (subtype_1 subtype*) : OK x i
        -- Subtype_ok2: C |- subtype_1 : OK x i
        -- Rectype_ok2: C |- REC subtype* : OK $(x+1) $(i+1)`. -/
  -- core-rule: Rectype_ok2/cons
  | cons {C : Context} {st : SubType} {sts : SubTypes} {x : TypeIdx} {i : Nat} :
      Subtype_ok2 C st x i →
      Rectype_ok2 C (.recr sts) (TypeIdx.ofNat (x.val + 1)) (i + 1) →
      Rectype_ok2 C (.recr (.cons st sts)) x i

/-- `relation Deftype_ok: context |- deftype : OK`. -/
inductive Deftype_ok : Context → DefType → Prop where
  /-- `rule Deftype_ok:
        C |- _DEF rectype i : OK
        -- Rectype_ok: C |- rectype : OK(x)
        -- if rectype = REC subtype^n
        -- if i < n`

  `x` occurs only in the premise, so it is existential, as SpecTec's free
  metavariables always are. -/
  -- core-rule: Deftype_ok
  | mk {C : Context} {qt : RecType} {i : Nat} {x : TypeIdx} :
      Rectype_ok C qt x → i < qt.count → Deftype_ok C (.defd qt i)

/-- `relation Heaptype_sub: context |- heaptype <: heaptype`. -/
inductive Heaptype_sub : Context → HeapType → HeapType → Prop where
  /-- `rule Heaptype_sub/refl: C |- heaptype <: heaptype`. -/
  -- core-rule: Heaptype_sub/refl
  | refl {C : Context} {ht : HeapType} : Heaptype_sub C ht ht
  /-- `rule Heaptype_sub/trans:
        C |- heaptype_1 <: heaptype_2
        -- Heaptype_ok: C |- heaptype' : OK
        -- Heaptype_sub: C |- heaptype_1 <: heaptype'
        -- Heaptype_sub: C |- heaptype' <: heaptype_2`. -/
  -- core-rule: Heaptype_sub/trans
  | trans {C : Context} {ht₁ ht₂ ht' : HeapType} :
      Heaptype_ok C ht' → Heaptype_sub C ht₁ ht' → Heaptype_sub C ht' ht₂ →
      Heaptype_sub C ht₁ ht₂
  /-- `rule Heaptype_sub/eq-any: C |- EQ <: ANY`. -/
  -- core-rule: Heaptype_sub/eq-any
  | eq_any {C : Context} : Heaptype_sub C (.abs .eq) (.abs .any)
  /-- `rule Heaptype_sub/i31-eq: C |- I31 <: EQ`. -/
  -- core-rule: Heaptype_sub/i31-eq
  | i31_eq {C : Context} : Heaptype_sub C (.abs .i31) (.abs .eq)
  /-- `rule Heaptype_sub/struct-eq: C |- STRUCT <: EQ`. -/
  -- core-rule: Heaptype_sub/struct-eq
  | struct_eq {C : Context} : Heaptype_sub C (.abs .struct) (.abs .eq)
  /-- `rule Heaptype_sub/array-eq: C |- ARRAY <: EQ`. -/
  -- core-rule: Heaptype_sub/array-eq
  | array_eq {C : Context} : Heaptype_sub C (.abs .array) (.abs .eq)
  /-- `rule Heaptype_sub/struct: C |- deftype <: STRUCT
      -- Expand: deftype ~~ STRUCT fieldtype*`. -/
  -- core-rule: Heaptype_sub/struct
  | struct {C : Context} {dt : DefType} {fts : FieldTypes} :
      Expand dt (.struct fts) → Heaptype_sub C (.use (.defd dt)) (.abs .struct)
  /-- `rule Heaptype_sub/array: C |- deftype <: ARRAY -- Expand: deftype ~~ ARRAY fieldtype`. -/
  -- core-rule: Heaptype_sub/array
  | array {C : Context} {dt : DefType} {ft : FieldType} :
      Expand dt (.array ft) → Heaptype_sub C (.use (.defd dt)) (.abs .array)
  /-- `rule Heaptype_sub/func: C |- deftype <: FUNC
      -- Expand: deftype ~~ FUNC t_1* -> t_2*`. -/
  -- core-rule: Heaptype_sub/func
  | func {C : Context} {dt : DefType} {dom cod : ValTypes} :
      Expand dt (.func dom cod) → Heaptype_sub C (.use (.defd dt)) (.abs .func)
  /-- `rule Heaptype_sub/def: C |- deftype_1 <: deftype_2
      -- Deftype_sub: C |- deftype_1 <: deftype_2`. -/
  -- core-rule: Heaptype_sub/def
  | def_ {C : Context} {dt₁ dt₂ : DefType} :
      Deftype_sub C dt₁ dt₂ → Heaptype_sub C (.use (.defd dt₁)) (.use (.defd dt₂))
  /-- `rule Heaptype_sub/typeidx-l: C |- _IDX typeidx <: heaptype
      -- Heaptype_sub: C |- C.TYPES[typeidx] <: heaptype`. -/
  -- core-rule: Heaptype_sub/typeidx-l
  | typeidx_l {C : Context} {x : TypeIdx} {dt : DefType} {ht : HeapType} :
      C.types[x.val]? = some dt → Heaptype_sub C (.use (.defd dt)) ht →
      Heaptype_sub C (.use (.idx x)) ht
  /-- `rule Heaptype_sub/typeidx-r: C |- heaptype <: _IDX typeidx
      -- Heaptype_sub: C |- heaptype <: C.TYPES[typeidx]`. -/
  -- core-rule: Heaptype_sub/typeidx-r
  | typeidx_r {C : Context} {ht : HeapType} {x : TypeIdx} {dt : DefType} :
      C.types[x.val]? = some dt → Heaptype_sub C ht (.use (.defd dt)) →
      Heaptype_sub C ht (.use (.idx x))
  /-- `rule Heaptype_sub/rec: C |- REC i <: typeuse*[j]
      -- if C.RECS[i] = SUB final? typeuse* ct`. -/
  -- core-rule: Heaptype_sub/rec
  | rec_ {C : Context} {i j : Nat} {fin : Option Final} {sups : TypeUses}
      {ct : CompType} {tu : TypeUse} :
      C.recs[i]? = some (.sub fin sups ct) →
      (TypeUses.toList sups)[j]? = some tu →
      Heaptype_sub C (.use (.recu i)) (.use tu)
  /-- `rule Heaptype_sub/none: C |- NONE <: heaptype -- Heaptype_sub: C |- heaptype <: ANY`. -/
  -- core-rule: Heaptype_sub/none
  | none_ {C : Context} {ht : HeapType} :
      Heaptype_sub C ht (.abs .any) → Heaptype_sub C (.abs .none) ht
  /-- `rule Heaptype_sub/nofunc: C |- NOFUNC <: heaptype
      -- Heaptype_sub: C |- heaptype <: FUNC`. -/
  -- core-rule: Heaptype_sub/nofunc
  | nofunc {C : Context} {ht : HeapType} :
      Heaptype_sub C ht (.abs .func) → Heaptype_sub C (.abs .nofunc) ht
  /-- `rule Heaptype_sub/noexn: C |- NOEXN <: heaptype
      -- Heaptype_sub: C |- heaptype <: EXN`. -/
  -- core-rule: Heaptype_sub/noexn
  | noexn {C : Context} {ht : HeapType} :
      Heaptype_sub C ht (.abs .exn) → Heaptype_sub C (.abs .noexn) ht
  /-- `rule Heaptype_sub/noextern: C |- NOEXTERN <: heaptype
      -- Heaptype_sub: C |- heaptype <: EXTERN`. -/
  -- core-rule: Heaptype_sub/noextern
  | noextern {C : Context} {ht : HeapType} :
      Heaptype_sub C ht (.abs .extern) → Heaptype_sub C (.abs .noextern) ht
  /-- `rule Heaptype_sub/bot: C |- BOT <: heaptype`. -/
  -- core-rule: Heaptype_sub/bot
  | bot {C : Context} {ht : HeapType} : Heaptype_sub C (.abs .bot) ht

/-- `relation Reftype_sub: context |- reftype <: reftype`. -/
inductive Reftype_sub : Context → RefType → RefType → Prop where
  /-- `rule Reftype_sub/nonnull: C |- REF ht_1 <: REF ht_2
      -- Heaptype_sub: C |- ht_1 <: ht_2`. -/
  -- core-rule: Reftype_sub/nonnull
  | nonnull {C : Context} {ht₁ ht₂ : HeapType} :
      Heaptype_sub C ht₁ ht₂ → Reftype_sub C (.ref none ht₁) (.ref none ht₂)
  /-- `rule Reftype_sub/null: C |- REF NULL? ht_1 <: REF NULL ht_2
      -- Heaptype_sub: C |- ht_1 <: ht_2`. -/
  -- core-rule: Reftype_sub/null
  | null {C : Context} {nul : Option Null} {ht₁ ht₂ : HeapType} :
      Heaptype_sub C ht₁ ht₂ → Reftype_sub C (.ref nul ht₁) (.ref (some .null) ht₂)

/-- `relation Valtype_sub: context |- valtype <: valtype`. -/
inductive Valtype_sub : Context → ValType → ValType → Prop where
  /-- `rule Valtype_sub/num: C |- numtype_1 <: numtype_2
      -- Numtype_sub: C |- numtype_1 <: numtype_2`. -/
  -- core-rule: Valtype_sub/num
  | num {C : Context} {nt₁ nt₂ : NumType} :
      Numtype_sub C nt₁ nt₂ → Valtype_sub C (.num nt₁) (.num nt₂)
  /-- `rule Valtype_sub/vec: C |- vectype_1 <: vectype_2
      -- Vectype_sub: C |- vectype_1 <: vectype_2`. -/
  -- core-rule: Valtype_sub/vec
  | vec {C : Context} {vt₁ vt₂ : VecType} :
      Vectype_sub C vt₁ vt₂ → Valtype_sub C (.vec vt₁) (.vec vt₂)
  /-- `rule Valtype_sub/ref: C |- reftype_1 <: reftype_2
      -- Reftype_sub: C |- reftype_1 <: reftype_2`. -/
  -- core-rule: Valtype_sub/ref
  | ref {C : Context} {rt₁ rt₂ : RefType} :
      Reftype_sub C rt₁ rt₂ → Valtype_sub C (.ref rt₁) (.ref rt₂)
  /-- `rule Valtype_sub/bot: C |- BOT <: valtype`. -/
  -- core-rule: Valtype_sub/bot
  | bot {C : Context} {t : ValType} : Valtype_sub C .bot t

/-- `relation Resulttype_sub: context |- resulttype <: resulttype`. -/
inductive Resulttype_sub : Context → List ValType → List ValType → Prop where
  /-- `rule Resulttype_sub: C |- t_1* <: t_2* -- (Valtype_sub: C |- t_1 <: t_2)*`. -/
  -- core-rule: Resulttype_sub
  | mk {C : Context} {ts₁ ts₂ : List ValType} :
      SeqLen₂ ts₁ ts₂ → SeqAll₂ (Valtype_sub C) ts₁ ts₂ → Resulttype_sub C ts₁ ts₂

/-- `relation Storagetype_sub: context |- storagetype <: storagetype`. -/
inductive Storagetype_sub : Context → StorageType → StorageType → Prop where
  /-- `rule Storagetype_sub/val: C |- valtype_1 <: valtype_2
      -- Valtype_sub: C |- valtype_1 <: valtype_2`. -/
  -- core-rule: Storagetype_sub/val
  | val {C : Context} {t₁ t₂ : ValType} :
      Valtype_sub C t₁ t₂ → Storagetype_sub C (.val t₁) (.val t₂)
  /-- `rule Storagetype_sub/pack: C |- packtype_1 <: packtype_2
      -- Packtype_sub: C |- packtype_1 <: packtype_2`. -/
  -- core-rule: Storagetype_sub/pack
  | pack {C : Context} {pt₁ pt₂ : PackType} :
      Packtype_sub C pt₁ pt₂ → Storagetype_sub C (.pack pt₁) (.pack pt₂)

/-- `relation Fieldtype_sub: context |- fieldtype <: fieldtype`. -/
inductive Fieldtype_sub : Context → FieldType → FieldType → Prop where
  /-- `rule Fieldtype_sub/const: C |- zt_1 <: zt_2
      -- Storagetype_sub: C |- zt_1 <: zt_2`: the immutable case, both fields
  written without `MUT`. -/
  -- core-rule: Fieldtype_sub/const
  | const {C : Context} {zt₁ zt₂ : StorageType} :
      Storagetype_sub C zt₁ zt₂ → Fieldtype_sub C (.mk none zt₁) (.mk none zt₂)
  /-- `rule Fieldtype_sub/var: C |- MUT zt_1 <: MUT zt_2
      -- Storagetype_sub: C |- zt_1 <: zt_2 -- Storagetype_sub: C |- zt_2 <: zt_1`. -/
  -- core-rule: Fieldtype_sub/var
  | var {C : Context} {zt₁ zt₂ : StorageType} :
      Storagetype_sub C zt₁ zt₂ → Storagetype_sub C zt₂ zt₁ →
      Fieldtype_sub C (.mk (some .mut) zt₁) (.mk (some .mut) zt₂)

/-- `relation Comptype_sub: context |- comptype <: comptype`, forward-declared
in `2.1-validation.types.spectec` and given its rules in `2.2`. -/
inductive Comptype_sub : Context → CompType → CompType → Prop where
  /-- `rule Comptype_sub/struct: C |- STRUCT (ft_1* ft'_1*) <: STRUCT ft_2*
      -- (Fieldtype_sub: C |- ft_1 <: ft_2)*`: width subtyping, the extra
  fields `ft'_1*` being unconstrained. -/
  -- core-rule: Comptype_sub/struct
  | struct {C : Context} {fts₁ fts₁' fts₂ : List FieldType} :
      SeqLen₂ fts₁ fts₂ → SeqAll₂ (Fieldtype_sub C) fts₁ fts₂ →
      Comptype_sub C (.struct (FieldTypes.ofList (fts₁ ++ fts₁')))
        (.struct (FieldTypes.ofList fts₂))
  /-- `rule Comptype_sub/array: C |- ARRAY ft_1 <: ARRAY ft_2
      -- Fieldtype_sub: C |- ft_1 <: ft_2`. -/
  -- core-rule: Comptype_sub/array
  | array {C : Context} {ft₁ ft₂ : FieldType} :
      Fieldtype_sub C ft₁ ft₂ → Comptype_sub C (.array ft₁) (.array ft₂)
  /-- `rule Comptype_sub/func: C |- FUNC t_11* -> t_12* <: FUNC t_21* -> t_22*
      -- Resulttype_sub: C |- t_21* <: t_11* -- Resulttype_sub: C |- t_12* <: t_22*`. -/
  -- core-rule: Comptype_sub/func
  | func {C : Context} {dom₁ cod₁ dom₂ cod₂ : ValTypes} :
      Resulttype_sub C (ValTypes.toList dom₂) (ValTypes.toList dom₁) →
      Resulttype_sub C (ValTypes.toList cod₁) (ValTypes.toList cod₂) →
      Comptype_sub C (.func dom₁ cod₁) (.func dom₂ cod₂)

/-- `relation Deftype_sub: context |- deftype <: deftype`, forward-declared in
`2.1-validation.types.spectec` and given its rules in `2.2`. -/
inductive Deftype_sub : Context → DefType → DefType → Prop where
  /-- `rule Deftype_sub/refl: C |- deftype_1 <: deftype_2
      -- if $clos_deftype(C, deftype_1) = $clos_deftype(C, deftype_2)`. -/
  -- core-rule: Deftype_sub/refl
  | refl {C : Context} {dt₁ dt₂ : DefType} :
      C.closDefType dt₁ = C.closDefType dt₂ → Deftype_sub C dt₁ dt₂
  /-- `rule Deftype_sub/super:
        C |- deftype_1 <: deftype_2
        -- if $unrolldt(deftype_1) = SUB final? typeuse* ct
        -- Heaptype_sub: C |- typeuse*[i] <: deftype_2`. -/
  -- core-rule: Deftype_sub/super
  | super {C : Context} {dt₁ dt₂ : DefType} {fin : Option Final} {sups : TypeUses}
      {ct : CompType} {i : Nat} {tu : TypeUse} :
      unrollDt dt₁ = some (.sub fin sups ct) →
      (TypeUses.toList sups)[i]? = some tu →
      Heaptype_sub C (.use tu) (.use (.defd dt₂)) →
      Deftype_sub C dt₁ dt₂

end

/-! ## Instruction types

`Instrtype_ok` and `Instrtype_sub` depend on the block above and nothing in it
depends on them. -/

/-- `relation Instrtype_ok: context |- instrtype : OK`. -/
inductive Instrtype_ok : Context → InstrType → Prop where
  /-- `rule Instrtype_ok:
        C |- t_1* ->_(x*) t_2* : OK
        -- Resulttype_ok: C |- t_1* : OK
        -- Resulttype_ok: C |- t_2* : OK
        -- (if C.LOCALS[x] = lct)*`. -/
  -- core-rule: Instrtype_ok
  | mk {C : Context} {it : InstrType} :
      Resulttype_ok C it.dom → Resulttype_ok C it.cod →
      SeqAll (fun (x : LocalIdx) => ∃ lct : LocalType, C.locals[x.val]? = some lct) it.locals →
      Instrtype_ok C it

/-- `relation Instrtype_sub: context |- instrtype <: instrtype`. -/
inductive Instrtype_sub : Context → InstrType → InstrType → Prop where
  /-- `rule Instrtype_sub:
        C |- t_11* ->_(x_1*) t_12* <: t_21* ->_(x_2*) t_22*
        -- Resulttype_sub: C |- t_21* <: t_11*
        -- Resulttype_sub: C |- t_12* <: t_22*
        -- if x* = $setminus_(localidx, x_2*, x_1*)
        -- (if C.LOCALS[x] = SET t)*`. -/
  -- core-rule: Instrtype_sub
  | mk {C : Context} {it₁ it₂ : InstrType} :
      Resulttype_sub C it₂.dom it₁.dom →
      Resulttype_sub C it₁.cod it₂.cod →
      SeqAll (fun (x : LocalIdx) => ∃ t : ValType, C.locals[x.val]? = some ⟨.set, t⟩)
        (setminus it₂.locals it₁.locals) →
      Instrtype_sub C it₁ it₂

/-! ## External types -/

/-- `relation Limits_ok: context |- limits : nat`. -/
inductive Limits_ok : Context → Limits → Nat → Prop where
  /-- `rule Limits_ok: C |- `[n .. m?] : k -- if n <= k -- (if n <= m <= k)?`. -/
  -- core-rule: Limits_ok
  | mk {C : Context} {lim : Limits} {k : Nat} :
      lim.min.val ≤ k →
      OptAll (fun (m : U64) => lim.min.val ≤ m.val ∧ m.val ≤ k) lim.max →
      Limits_ok C lim k

/-- `relation Tagtype_ok: context |- tagtype : OK`. -/
inductive Tagtype_ok : Context → TagType → Prop where
  /-- `rule Tagtype_ok:
        C |- typeuse : OK
        -- Typeuse_ok: C |- typeuse : OK
        -- Expand_use: typeuse ~~_C $($(FUNC t_1* -> t_2*))`. -/
  -- core-rule: Tagtype_ok
  | mk {C : Context} {jt : TagType} {dom cod : ValTypes} :
      Typeuse_ok C jt → Expand_use C jt (.func dom cod) → Tagtype_ok C jt

/-- `relation Globaltype_ok: context |- globaltype : OK`. -/
inductive Globaltype_ok : Context → GlobalType → Prop where
  /-- `rule Globaltype_ok: C |- MUT? t : OK -- Valtype_ok: C |- t : OK`. -/
  -- core-rule: Globaltype_ok
  | mk {C : Context} {gt : GlobalType} : Valtype_ok C gt.valtype → Globaltype_ok C gt

/-- `relation Memtype_ok: context |- memtype : OK`. -/
inductive Memtype_ok : Context → MemType → Prop where
  /-- `rule Memtype_ok: C |- addrtype limits PAGE : OK
      -- Limits_ok: C |- limits : $(2^16)`. -/
  -- core-rule: Memtype_ok
  | mk {C : Context} {mt : MemType} : Limits_ok C mt.lim (2 ^ 16) → Memtype_ok C mt

/-- `relation Tabletype_ok: context |- tabletype : OK`. -/
inductive Tabletype_ok : Context → TableType → Prop where
  /-- `rule Tabletype_ok:
        C |- addrtype limits reftype : OK
        -- Limits_ok: C |- limits : $(2^32 - 1)
        -- Reftype_ok: C |- reftype : OK`. -/
  -- core-rule: Tabletype_ok
  | mk {C : Context} {tt : TableType} :
      Limits_ok C tt.lim (2 ^ 32 - 1) → Reftype_ok C tt.elem → Tabletype_ok C tt

/-- `relation Externtype_ok: context |- externtype : OK`. -/
inductive Externtype_ok : Context → ExternType → Prop where
  /-- `rule Externtype_ok/tag: C |- TAG tagtype : OK -- Tagtype_ok: C |- tagtype : OK`. -/
  -- core-rule: Externtype_ok/tag
  | tag {C : Context} {jt : TagType} : Tagtype_ok C jt → Externtype_ok C (.tag jt)
  /-- `rule Externtype_ok/global: C |- GLOBAL globaltype : OK
      -- Globaltype_ok: C |- globaltype : OK`. -/
  -- core-rule: Externtype_ok/global
  | global {C : Context} {gt : GlobalType} : Globaltype_ok C gt → Externtype_ok C (.global gt)
  /-- `rule Externtype_ok/mem: C |- MEM memtype : OK -- Memtype_ok: C |- memtype : OK`. -/
  -- core-rule: Externtype_ok/mem
  | mem {C : Context} {mt : MemType} : Memtype_ok C mt → Externtype_ok C (.mem mt)
  /-- `rule Externtype_ok/table: C |- TABLE tabletype : OK
      -- Tabletype_ok: C |- tabletype : OK`. -/
  -- core-rule: Externtype_ok/table
  | table {C : Context} {tt : TableType} : Tabletype_ok C tt → Externtype_ok C (.table tt)
  /-- `rule Externtype_ok/func:
        C |- FUNC typeuse : OK
        -- Typeuse_ok: C |- typeuse : OK
        -- Expand_use: typeuse ~~_C $($(FUNC t_1* -> t_2*))`. -/
  -- core-rule: Externtype_ok/func
  | func {C : Context} {tu : TypeUse} {dom cod : ValTypes} :
      Typeuse_ok C tu → Expand_use C tu (.func dom cod) → Externtype_ok C (.func tu)

/-! ## External subtyping -/

/-- `relation Limits_sub: context |- limits <: limits`. -/
inductive Limits_sub : Context → Limits → Limits → Prop where
  /-- `rule Limits_sub: C |- `[n_1 .. m_1] <: `[n_2 .. m_2]
      -- if n_1 >= n_2 -- if m_1 <= m_2`.

  Both maxima are matched WITHOUT a `?` in the pinned source, unlike
  `Limits_ok`'s `m?`; the rule therefore relates only limits that both carry a
  maximum.  Transcribed as written. -/
  -- core-rule: Limits_sub
  | mk {C : Context} {n₁ n₂ m₁ m₂ : U64} :
      n₂.val ≤ n₁.val → m₁.val ≤ m₂.val →
      Limits_sub C ⟨n₁, some m₁⟩ ⟨n₂, some m₂⟩

/-- `relation Tagtype_sub: context |- tagtype <: tagtype`. -/
inductive Tagtype_sub : Context → TagType → TagType → Prop where
  /-- `rule Tagtype_sub:
        C |- deftype_1 <: deftype_2
        -- Deftype_sub: C |- deftype_1 <: deftype_2
        -- Deftype_sub: C |- deftype_2 <: deftype_1`

  The rule matches both tag types as `deftype`s, so the conclusion is on the
  `typeuse/sem` fragment. -/
  -- core-rule: Tagtype_sub
  | mk {C : Context} {dt₁ dt₂ : DefType} :
      Deftype_sub C dt₁ dt₂ → Deftype_sub C dt₂ dt₁ →
      Tagtype_sub C (.defd dt₁) (.defd dt₂)

/-- `relation Globaltype_sub: context |- globaltype <: globaltype`. -/
inductive Globaltype_sub : Context → GlobalType → GlobalType → Prop where
  /-- `rule Globaltype_sub/const: C |- valtype_1 <: valtype_2
      -- Valtype_sub: C |- valtype_1 <: valtype_2`. -/
  -- core-rule: Globaltype_sub/const
  | const {C : Context} {t₁ t₂ : ValType} :
      Valtype_sub C t₁ t₂ → Globaltype_sub C ⟨none, t₁⟩ ⟨none, t₂⟩
  /-- `rule Globaltype_sub/var: C |- MUT valtype_1 <: MUT valtype_2
      -- Valtype_sub: C |- valtype_1 <: valtype_2 -- Valtype_sub: C |- valtype_2 <: valtype_1`. -/
  -- core-rule: Globaltype_sub/var
  | var {C : Context} {t₁ t₂ : ValType} :
      Valtype_sub C t₁ t₂ → Valtype_sub C t₂ t₁ →
      Globaltype_sub C ⟨some .mut, t₁⟩ ⟨some .mut, t₂⟩

/-- `relation Memtype_sub: context |- memtype <: memtype`. -/
inductive Memtype_sub : Context → MemType → MemType → Prop where
  /-- `rule Memtype_sub: C |- addrtype limits_1 PAGE <: addrtype limits_2 PAGE
      -- Limits_sub: C |- limits_1 <: limits_2`: the SAME `addrtype` on both
  sides, as the source writes it. -/
  -- core-rule: Memtype_sub
  | mk {C : Context} {at_ : AddrType} {lim₁ lim₂ : Limits} :
      Limits_sub C lim₁ lim₂ → Memtype_sub C ⟨at_, lim₁⟩ ⟨at_, lim₂⟩

/-- `relation Tabletype_sub: context |- tabletype <: tabletype`. -/
inductive Tabletype_sub : Context → TableType → TableType → Prop where
  /-- `rule Tabletype_sub:
        C |- addrtype limits_1 reftype_1 <: addrtype limits_2 reftype_2
        -- Limits_sub: C |- limits_1 <: limits_2
        -- Reftype_sub: C |- reftype_1 <: reftype_2
        -- Reftype_sub: C |- reftype_2 <: reftype_1`. -/
  -- core-rule: Tabletype_sub
  | mk {C : Context} {at_ : AddrType} {lim₁ lim₂ : Limits} {rt₁ rt₂ : RefType} :
      Limits_sub C lim₁ lim₂ → Reftype_sub C rt₁ rt₂ → Reftype_sub C rt₂ rt₁ →
      Tabletype_sub C ⟨at_, lim₁, rt₁⟩ ⟨at_, lim₂, rt₂⟩

/-- `relation Externtype_sub: context |- externtype <: externtype`. -/
inductive Externtype_sub : Context → ExternType → ExternType → Prop where
  /-- `rule Externtype_sub/tag: C |- TAG tagtype_1 <: TAG tagtype_2
      -- Tagtype_sub: C |- tagtype_1 <: tagtype_2`. -/
  -- core-rule: Externtype_sub/tag
  | tag {C : Context} {jt₁ jt₂ : TagType} :
      Tagtype_sub C jt₁ jt₂ → Externtype_sub C (.tag jt₁) (.tag jt₂)
  /-- `rule Externtype_sub/global: C |- GLOBAL globaltype_1 <: GLOBAL globaltype_2
      -- Globaltype_sub: C |- globaltype_1 <: globaltype_2`. -/
  -- core-rule: Externtype_sub/global
  | global {C : Context} {gt₁ gt₂ : GlobalType} :
      Globaltype_sub C gt₁ gt₂ → Externtype_sub C (.global gt₁) (.global gt₂)
  /-- `rule Externtype_sub/mem: C |- MEM memtype_1 <: MEM memtype_2
      -- Memtype_sub: C |- memtype_1 <: memtype_2`. -/
  -- core-rule: Externtype_sub/mem
  | mem {C : Context} {mt₁ mt₂ : MemType} :
      Memtype_sub C mt₁ mt₂ → Externtype_sub C (.mem mt₁) (.mem mt₂)
  /-- `rule Externtype_sub/table: C |- TABLE tabletype_1 <: TABLE tabletype_2
      -- Tabletype_sub: C |- tabletype_1 <: tabletype_2`. -/
  -- core-rule: Externtype_sub/table
  | table {C : Context} {tt₁ tt₂ : TableType} :
      Tabletype_sub C tt₁ tt₂ → Externtype_sub C (.table tt₁) (.table tt₂)
  /-- `rule Externtype_sub/func: C |- FUNC deftype_1 <: FUNC deftype_2
      -- Deftype_sub: C |- deftype_1 <: deftype_2`: the rule matches both
  payloads as `deftype`s. -/
  -- core-rule: Externtype_sub/func
  | func {C : Context} {dt₁ dt₂ : DefType} :
      Deftype_sub C dt₁ dt₂ → Externtype_sub C (.func (.defd dt₁)) (.func (.defd dt₂))

/-! ## Sanity checks

A transcription of a typing judgment is worth nothing if the judgment turns out
to be empty, or if a rule that should chain does not.  These are kernel-checked
derivations, not tests. -/

/-- `Valtype_ok` is inhabited: `I32` is a well-formed value type. -/
example : Valtype_ok Context.empty (.num .i32) := .num .mk

/-- `BOT` is a well-formed value type and a subtype of everything --- the two
`/sem`-fragment rules the previous i32-only validator had no room for. -/
example : Valtype_sub Context.empty .bot (.vec .v128) := .bot

/-- The GC bottom types chain through the abstract hierarchy:
`NONE <: EQ` because `EQ <: ANY`. -/
example : Heaptype_sub Context.empty (.abs .none) (.abs .eq) := .none_ .eq_any

/-- `NOEXN <: EXN`, the exception-handling corner of the same hierarchy. -/
example : Heaptype_sub Context.empty (.abs .noexn) (.abs .exn) := .noexn .refl

/-- Reference subtyping loses nullability in the right direction:
`(REF I31)` is a subtype of `(REF NULL EQ)`. -/
example :
    Reftype_sub Context.empty (.ref none (.abs .i31)) (.ref (some .null) (.abs .eq)) :=
  .null .i31_eq

/-- An empty result type is well-formed. -/
example : Resulttype_ok Context.empty [] := .mk (fun _ h => nomatch h)

/-- A memory type whose limits are `[1 .. 2]` is well-formed: `Limits_ok` is
checked against `2^16`. -/
example :
    Memtype_ok Context.empty
      { addr := .i32, lim := { min := ⟨1, by decide⟩, max := some ⟨2, by decide⟩ } } :=
  .mk (.mk (by decide) (fun m h => by cases h; exact ⟨by decide, by decide⟩))

end WasmGemmGnaf.Wasm.Core
