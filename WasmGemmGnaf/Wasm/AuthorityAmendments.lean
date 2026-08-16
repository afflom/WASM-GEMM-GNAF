/-
  Wasm/AuthorityAmendments.lean --- canonical identities for the explicit
  repairs carried against the byte-identical pinned Core 3.0 source tree.

  The vendored files are authority and are never edited.  Each row below binds
  an amendment to the exact source digest and exact removed/inserted text.  The
  effect is data only; semantic claims about an amendment are proved in the
  corresponding coverage-neutral `*Amended.lean` layer.
-/
import WasmGemmGnaf.Wasm.Revision

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm

open WasmGemmGnaf.Foundation

deriving instance Inhabited for CanonicalObjectId

/-- How an exact authority patch changes the pinned relation. -/
inductive AuthorityPatchEffect
  | add
  | replace
  | narrow
  | widen
  deriving DecidableEq, Inhabited

namespace AuthorityPatchEffect

def tag : AuthorityPatchEffect → UInt8
  | .add => 0
  | .replace => 1
  | .narrow => 2
  | .widen => 3

theorem tag_injective : Function.Injective tag := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def bytes (e : AuthorityPatchEffect) : List UInt8 := Bytes.u8Bytes e.tag

theorem bytes_prefixFree : Bytes.PrefixFree bytes :=
  Bytes.u8Bytes_prefixFree.comp tag_injective

end AuthorityPatchEffect

/-- One exact textual operation against one digest-bound vendored source. -/
structure AuthorityPatchBody where
  sourcePath : String
  sourceSha256 : String
  beforeAnchor : String
  afterAnchor : String
  removedText : String
  insertedText : String
  effect : AuthorityPatchEffect
  affectedAuthoritySymbols : List String
  amendedLeanDeclarations : List String
  deriving DecidableEq, Inhabited

namespace AuthorityPatchBody

def headerStrings (p : AuthorityPatchBody) : List String :=
  [p.sourcePath, p.sourceSha256, p.beforeAnchor, p.afterAnchor,
    p.removedText, p.insertedText]

def bytes (p : AuthorityPatchBody) : List UInt8 :=
  Enc.stringsBytes p.headerStrings ++
    (AuthorityPatchEffect.bytes p.effect ++
      (Enc.stringsBytes p.affectedAuthoritySymbols ++
        Enc.stringsBytes p.amendedLeanDeclarations))

theorem bytes_prefixFree : Bytes.PrefixFree bytes := by
  intro x y r s h
  simp only [bytes, List.append_assoc] at h
  obtain ⟨h1, h⟩ := Enc.stringsBytes_prefixFree _ _ _ _ h
  obtain ⟨h2, h⟩ := AuthorityPatchEffect.bytes_prefixFree _ _ _ _ h
  obtain ⟨h3, h⟩ := Enc.stringsBytes_prefixFree _ _ _ _ h
  obtain ⟨h4, h⟩ := Enc.stringsBytes_prefixFree _ _ _ _ h
  refine ⟨?_, h⟩
  cases x
  cases y
  simp only [headerStrings, List.cons.injEq, and_true] at h1
  simp_all

theorem bytes_injective : Function.Injective bytes :=
  bytes_prefixFree.injective

def identitySchema : CanonicalSchema AuthorityPatchBody :=
  CanonicalSchema.ofPrefixFree 1 .authority
    (TypeTag.leaf (Enc.nameBytes "wasm.authority.patch.body/1"))
    (TypeTag.leaf_size_pos _)
    bytes bytes_prefixFree

def identity (p : AuthorityPatchBody) : CanonicalObjectId :=
  CanonicalObjectId.ofTyped (Identity identitySchema p)

theorem identity_eq_iff {a b : AuthorityPatchBody} :
    identity a = identity b ↔ a = b :=
  CanonicalObjectId.ofTyped_Identity_eq_iff identitySchema

end AuthorityPatchBody

/-- A SPEC amendment and the exact authority patch operations it authorizes. -/
structure AuthorityAmendmentBody where
  deviationId : String
  amendmentId : String
  specSection : String
  pinnedCommit : String
  patches : List AuthorityPatchBody
  upstreamReferences : List String
  deriving DecidableEq, Inhabited

namespace AuthorityAmendmentBody

def headerStrings (a : AuthorityAmendmentBody) : List String :=
  [a.deviationId, a.amendmentId, a.specSection, a.pinnedCommit]

def patchListBytes (ps : List AuthorityPatchBody) : List UInt8 :=
  Bytes.listBytes AuthorityPatchBody.bytes ps

theorem patchListBytes_prefixFree : Bytes.PrefixFree patchListBytes :=
  Bytes.listBytes_prefixFree AuthorityPatchBody.bytes_prefixFree

def bytes (a : AuthorityAmendmentBody) : List UInt8 :=
  Enc.stringsBytes a.headerStrings ++
    (patchListBytes a.patches ++ Enc.stringsBytes a.upstreamReferences)

theorem bytes_prefixFree : Bytes.PrefixFree bytes := by
  intro x y r s h
  simp only [bytes, List.append_assoc] at h
  obtain ⟨h1, h⟩ := Enc.stringsBytes_prefixFree _ _ _ _ h
  obtain ⟨h2, h⟩ := patchListBytes_prefixFree _ _ _ _ h
  obtain ⟨h3, h⟩ := Enc.stringsBytes_prefixFree _ _ _ _ h
  refine ⟨?_, h⟩
  cases x
  cases y
  simp only [headerStrings, List.cons.injEq, and_true] at h1
  simp_all

theorem bytes_injective : Function.Injective bytes :=
  bytes_prefixFree.injective

def identitySchema : CanonicalSchema AuthorityAmendmentBody :=
  CanonicalSchema.ofPrefixFree 1 .authority
    (TypeTag.leaf (Enc.nameBytes "wasm.authority.amendment.body/1"))
    (TypeTag.leaf_size_pos _)
    bytes bytes_prefixFree

def identity (a : AuthorityAmendmentBody) : CanonicalObjectId :=
  CanonicalObjectId.ofTyped (Identity identitySchema a)

theorem identity_eq_iff {a b : AuthorityAmendmentBody} :
    identity a = identity b ↔ a = b :=
  CanonicalObjectId.ofTyped_Identity_eq_iff identitySchema

end AuthorityAmendmentBody

/-- The canonical set of repairs carried against one exact vendored tree. -/
structure AuthorityAmendmentSetBody where
  vendoredTreeId : CanonicalObjectId
  amendments : List AuthorityAmendmentBody
  deriving DecidableEq, Inhabited

namespace AuthorityAmendmentSetBody

def amendmentListBytes (as : List AuthorityAmendmentBody) : List UInt8 :=
  Bytes.listBytes AuthorityAmendmentBody.bytes as

theorem amendmentListBytes_prefixFree : Bytes.PrefixFree amendmentListBytes :=
  Bytes.listBytes_prefixFree AuthorityAmendmentBody.bytes_prefixFree

def bytes (s : AuthorityAmendmentSetBody) : List UInt8 :=
  CanonicalObjectId.bytes s.vendoredTreeId ++ amendmentListBytes s.amendments

theorem bytes_prefixFree : Bytes.PrefixFree bytes := by
  intro x y r s h
  simp only [bytes, List.append_assoc] at h
  obtain ⟨h1, h⟩ := CanonicalObjectId.bytes_prefixFree _ _ _ _ h
  obtain ⟨h2, h⟩ := amendmentListBytes_prefixFree _ _ _ _ h
  refine ⟨?_, h⟩
  cases x
  cases y
  simp_all

theorem bytes_injective : Function.Injective bytes :=
  bytes_prefixFree.injective

def identitySchema : CanonicalSchema AuthorityAmendmentSetBody :=
  CanonicalSchema.ofPrefixFree 1 .authority
    (TypeTag.leaf (Enc.nameBytes "wasm.authority.amendment.set.body/1"))
    (TypeTag.leaf_size_pos _)
    bytes bytes_prefixFree

/-
  Keep the identity's *data* independent of the proof stored in
  `identitySchema`.  The two definitions reduce to the same four fields, but
  constructing the value through `CanonicalSchema.ofPrefixFree` retains that
  schema's injectivity proof in the environment dependency of the result.  In
  particular, the proof of `AuthorityPatchBody.bytes_prefixFree` uses
  classical reasoning, so routing this Type-valued identity through the schema
  would make every `Wasm.Profile` -- and therefore every executable raw-input
  enumerator indexed by a profile -- depend on `Classical.choice`.

  Identity comparison remains structural: `identity_eq_iff` below is proved
  from the same frozen schema.  This constructor changes no encoded byte and
  carries no proof field.
-/
def identity (s : AuthorityAmendmentSetBody) : CanonicalObjectId :=
  { schemaVersion := 1
    domain := .authority
    typeTag := TypeTag.leaf (Enc.nameBytes "wasm.authority.amendment.set.body/1")
    canonicalBodyBytes := Bytes.pack (bytes s) }

/-- The proof-free constructor is byte-for-byte the identity produced by the
frozen injective schema. -/
theorem identity_eq_schema (s : AuthorityAmendmentSetBody) :
    identity s = CanonicalObjectId.ofTyped (Identity identitySchema s) :=
  rfl

theorem identity_eq_iff {a b : AuthorityAmendmentSetBody} :
    identity a = identity b ↔ a = b :=
  CanonicalObjectId.ofTyped_Identity_eq_iff identitySchema

end AuthorityAmendmentSetBody

/-! ## Exact Core 3.0 repair set -/

private def authoritySource (leaf : String) : String :=
  "vendor/wasm-spec/specification/wasm-3.0/" ++ leaf

def core3InstrSeqAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-006"
    amendmentId := "AMD-005"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "2.3-validation.instructions.spectec"
         sourceSha256 :=
           "a83d9b3ea01740f86c966ad256d6b484779ac40722a9568de021514537506bc1"
         beforeAnchor := "rule Instrs_ok/seq:"
         afterAnchor := "rule Instrs_ok/sub:"
         removedText :=
           "C |- instr_1 instr_2* : t_1* ->_(x_1* x_2*) t_3*\n-- Instr_ok: C |- instr_1 : t_1* ->_(x_1*) t_2*\n-- (if C.LOCALS[x_1] = init t)*\n-- Instrs_ok: $with_locals(C, x_1*, (SET t)*) |- instr_2* : t_2* ->_(x_2*) t_3*"
         insertedText :=
           "C |- instr_1 instr_2* : (t_0* t_1*) ->_(x_1* x_2*) t_3*\n-- Instr_ok: C |- instr_1 : t_1* ->_(x_1*) t_2*\n-- Valtypes_ok: C |- t_0* : OK\n-- (if C.LOCALS[x_1] = init t)*\n-- Instrs_ok: $with_locals(C, x_1*, (SET t)*) |- instr_2* : (t_0* t_2*) ->_(x_2*) t_3*"
         effect := .widen
         affectedAuthoritySymbols := ["Instrs_ok/seq"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Instr_okA",
            "WasmGemmGnaf.Wasm.Core.Instrs_okA",
            "WasmGemmGnaf.Wasm.Core.Expr_okA",
            "WasmGemmGnaf.Wasm.Core.Func_okA"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/issues/2194",
       "https://github.com/WebAssembly/spec/pull/2197",
       "bd4633aced30b720ff62b44cf00c03ece792f008"] }

def core3SignedLebAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-007"
    amendmentId := "AMD-007"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "5.1-binary.values.spectec"
         sourceSha256 :=
           "6709c273b1241eeb9b3ff84cfa05ccd36b2b07a749bca77b1f68d1c1d7c0a54d"
         beforeAnchor := "grammar BsN(N)"
         afterAnchor := "grammar BiN(N)"
         removedText := "| n:Bbyte i:BuN(($(N-7))) => $(2^7 * i + (n - 2^7))"
         insertedText := "| n:Bbyte i:BsN(($(N-7))) => $(2^7 * i + (n - 2^7))"
         effect := .narrow
         affectedAuthoritySymbols := ["BsN"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Binary.BsN'",
            "WasmGemmGnaf.Wasm.Core.Decode.decSN'"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/main/specification/wasm-3.0/5.1-binary.values.spectec"] }

def core3PromoteOpcodeAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-008"
    amendmentId := "AMD-008"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "5.3-binary.instructions.spectec"
         sourceSha256 :=
           "14a88a4c5398e58a33a298f68508d76cbbfc308a4dd9e456fe34d5f12a465bc5"
         beforeAnchor := "grammar Binstr/num-cvt"
         afterAnchor := "| 0xBC => CVTOP I32 F32 REINTERPRET"
         removedText := "| 0xBB => CVTOP F32 F64 PROMOTE"
         insertedText := "| 0xBB => CVTOP F64 F32 PROMOTE"
         effect := .replace
         affectedAuthoritySymbols := ["Binstr/num-cvt", "0xBB"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Binary.BinstrNum'",
            "WasmGemmGnaf.Wasm.Core.Decode.op0'"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/main/specification/wasm-3.0/5.3-binary.instructions.spectec"] }

def core3ExceptionFreeAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-009"
    amendmentId := "AMD-009"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "1.1-syntax.values.spectec"
         sourceSha256 :=
           "743ba8743488ce9ed99472c8441d0dae2263f11d96f525481275f8bc7b93bea8"
         beforeAnchor := "syntax free ="
         afterAnchor := "def $free_opt(free?) : free"
         removedText := "    LABELS labelidx*\n  }"
         insertedText := "    LABELS labelidx*,\n    TAGS tagidx*\n  }"
         effect := .add
         affectedAuthoritySymbols := ["free", "TAGS"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.Free'"] },
       { sourcePath := authoritySource "1.1-syntax.values.spectec"
         sourceSha256 :=
           "743ba8743488ce9ed99472c8441d0dae2263f11d96f525481275f8bc7b93bea8"
         beforeAnchor := "def $free_externidx(externidx) : free"
         afterAnchor := "def $free_typeidx(typeidx) = {TYPES typeidx}"
         removedText := ""
         insertedText := "def $free_tagidx(tagidx) : free"
         effect := .add
         affectedAuthoritySymbols := ["$free_tagidx"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.Free'.ofTagIdx"] },
       { sourcePath := authoritySource "1.1-syntax.values.spectec"
         sourceSha256 :=
           "743ba8743488ce9ed99472c8441d0dae2263f11d96f525481275f8bc7b93bea8"
         beforeAnchor := "def $free_labelidx(labelidx) = {LABELS labelidx}"
         afterAnchor := "def $free_externidx(FUNC funcidx)"
         removedText := ""
         insertedText := "def $free_tagidx(tagidx) = {TAGS tagidx}"
         effect := .add
         affectedAuthoritySymbols := ["$free_tagidx"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.Free'.ofTagIdx"] },
       { sourcePath := authoritySource "1.1-syntax.values.spectec"
         sourceSha256 :=
           "743ba8743488ce9ed99472c8441d0dae2263f11d96f525481275f8bc7b93bea8"
         beforeAnchor := "def $free_externidx(MEM memidx) = $free_memidx(memidx)"
         afterAnchor := ""
         removedText := ""
         insertedText := "def $free_externidx(TAG tagidx) = $free_tagidx(tagidx)"
         effect := .add
         affectedAuthoritySymbols := ["$free_externidx/TAG"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.Free'.ofExternIdx"] },
       { sourcePath := authoritySource "1.3-syntax.instructions.spectec"
         sourceSha256 :=
           "b3cf46cd6b94b6baba89b7be3f3b10a1d38f2f2127b41939b4e6be53b5ab3cd9"
         beforeAnchor := "def $free_blocktype(blocktype) : free"
         afterAnchor := "def $free_instr(instr) : free"
         removedText := ""
         insertedText := "def $free_catch(catch) : free"
         effect := .add
         affectedAuthoritySymbols := ["$free_catch"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.freeCatch'"] },
       { sourcePath := authoritySource "1.3-syntax.instructions.spectec"
         sourceSha256 :=
           "b3cf46cd6b94b6baba89b7be3f3b10a1d38f2f2127b41939b4e6be53b5ab3cd9"
         beforeAnchor := "def $free_blocktype(_IDX typeidx) = $free_typeidx(typeidx)"
         afterAnchor := "def $free_instr(NOP) = {}"
         removedText := ""
         insertedText :=
           "def $free_catch(CATCH tagidx labelidx) = $free_tagidx(tagidx) ++ $free_labelidx(labelidx)\ndef $free_catch(CATCH_REF tagidx labelidx) = $free_tagidx(tagidx) ++ $free_labelidx(labelidx)\ndef $free_catch(CATCH_ALL labelidx) = $free_labelidx(labelidx)\ndef $free_catch(CATCH_ALL_REF labelidx) = $free_labelidx(labelidx)"
         effect := .add
         affectedAuthoritySymbols := ["$free_catch/CATCH", "$free_catch/CATCH_REF",
           "$free_catch/CATCH_ALL", "$free_catch/CATCH_ALL_REF"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.freeCatch'"] },
       { sourcePath := authoritySource "1.3-syntax.instructions.spectec"
         sourceSha256 :=
           "b3cf46cd6b94b6baba89b7be3f3b10a1d38f2f2127b41939b4e6be53b5ab3cd9"
         beforeAnchor :=
           "def $free_instr(RETURN_CALL_INDIRECT tableidx typeuse) ="
         afterAnchor := "def $free_instr(CONST numtype numlit)"
         removedText := ""
         insertedText :=
           "def $free_instr(THROW tagidx) = $free_tagidx(tagidx)\ndef $free_instr(THROW_REF) = {}\ndef $free_instr(TRY_TABLE blocktype catch* instr*) =\n  $free_blocktype(blocktype) ++ $free_list($free_catch(catch)*) ++ $free_list($free_instr(instr)*)"
         effect := .add
         affectedAuthoritySymbols := ["$free_instr/THROW",
           "$free_instr/THROW_REF", "$free_instr/TRY_TABLE"]
         amendedLeanDeclarations := ["WasmGemmGnaf.Wasm.Core.freeInstr'"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/main/specification/wasm-3.0/1.1-syntax.values.spectec",
       "https://github.com/WebAssembly/spec/blob/main/specification/wasm-3.0/1.3-syntax.instructions.spectec"] }

def core3CallRefAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-010"
    amendmentId := "AMD-010"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "5.3-binary.instructions.spectec"
         sourceSha256 :=
           "14a88a4c5398e58a33a298f68508d76cbbfc308a4dd9e456fe34d5f12a465bc5"
         beforeAnchor := "| 0x13 y:Btypeidx x:Btableidx => RETURN_CALL_INDIRECT x (_IDX y)"
         afterAnchor := "| 0x1F bt:Bblocktype"
         removedText := ""
         insertedText :=
           "| 0x14 x:Btypeidx => CALL_REF (_IDX x)\n| 0x15 x:Btypeidx => RETURN_CALL_REF (_IDX x)"
         effect := .add
         affectedAuthoritySymbols := ["Binstr/control", "0x14", "0x15"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Binary.BinstrControl'",
            "WasmGemmGnaf.Wasm.Core.Decode.decOp1'"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/main/specification/wasm-3.0/5.3-binary.instructions.spectec"] }

def core3BottomSubtypingAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-011"
    amendmentId := "AMD-011"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "2.2-validation.subtyping.spectec"
         sourceSha256 :=
           "71ebcb2a53e55b8246c139e70ffbe7f4885c45eb757f8e7138e1563014cd432f"
         beforeAnchor := "rule Heaptype_sub/none:"
         afterAnchor := "rule Heaptype_sub/bot:"
         removedText :=
           "C |- NONE <: heaptype\n-- Heaptype_sub: C |- heaptype <: ANY\nC |- NOFUNC <: heaptype\n-- Heaptype_sub: C |- heaptype <: FUNC\nC |- NOEXN <: heaptype\n-- Heaptype_sub: C |- heaptype <: EXN\nC |- NOEXTERN <: heaptype\n-- Heaptype_sub: C |- heaptype <: EXTERN"
         insertedText :=
           "C |- NONE <: heaptype\n-- if heaptype =/= BOT\n-- Heaptype_sub: C |- heaptype <: ANY\nC |- NOFUNC <: heaptype\n-- if heaptype =/= BOT\n-- Heaptype_sub: C |- heaptype <: FUNC\nC |- NOEXN <: heaptype\n-- if heaptype =/= BOT\n-- Heaptype_sub: C |- heaptype <: EXN\nC |- NOEXTERN <: heaptype\n-- if heaptype =/= BOT\n-- Heaptype_sub: C |- heaptype <: EXTERN"
         effect := .narrow
         affectedAuthoritySymbols := ["Heaptype_sub/none", "Heaptype_sub/nofunc",
           "Heaptype_sub/noexn", "Heaptype_sub/noextern"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Heaptype_subA",
            "WasmGemmGnaf.Wasm.Core.decHeaptypeSub"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/main/specification/wasm-3.0/2.2-validation.subtyping.spectec"] }

/-- DEV-012: opcode 275's pinned vector shape violates the independently
transcribed `vextternop__` family premise.  The release relation replaces only
that malformed abstract instruction; the opcode bytes are unchanged. -/
def core3RelaxedDotAddAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-012"
    amendmentId := "AMD-012"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "5.3-binary.instructions.spectec"
         sourceSha256 :=
           "14a88a4c5398e58a33a298f68508d76cbbfc308a4dd9e456fe34d5f12a465bc5"
         beforeAnchor := "grammar Binstr/vec-exttern-i32x4 : instr = ..."
         afterAnchor := "grammar Binstr/vec-un-i64x2 : instr = ..."
         removedText :=
           "| 0xFD 275:Bu32 => VEXTTERNOP (I32 X `4) (I16 X `8) RELAXED_DOT_ADD S"
         insertedText :=
           "| 0xFD 275:Bu32 => VEXTTERNOP (I32 X `4) (I8 X `16) RELAXED_DOT_ADD S"
         effect := .replace
         affectedAuthoritySymbols := ["Binstr/vec-exttern-i32x4", "0xFD 275"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Binary.BinstrVecInt32And64'",
            "WasmGemmGnaf.Wasm.Core.Decode.opFD0For",
            "WasmGemmGnaf.Wasm.Core.Binary.encFD0InstrFor"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/9d36019973201a19f9c9ebb0f10828b2fe2374aa/specification/wasm-3.0/1.3-syntax.instructions.spectec",
       "https://github.com/WebAssembly/spec/blob/9d36019973201a19f9c9ebb0f10828b2fe2374aa/test/core/relaxed-simd/relaxed_dot_product.wast"] }

/-- DEV-013: the pinned generalized-subtype validity rule omits validity of
each declared generalized supertype.  The release relation adds exactly the
premise later merged upstream for WebAssembly/spec#2141; the subtyping rules
themselves remain unchanged. -/
def core3SupertypeValidityAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-013"
    amendmentId := "AMD-013"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "2.1-validation.types.spectec"
         sourceSha256 :=
           "4b5836e27d39b78a9b29dcdf5be9493abebdaabbcb7f76ef3dfd84b2870c789b"
         beforeAnchor := "rule Subtype_ok2:"
         afterAnchor := "rule Rectype_ok/empty:"
         removedText :=
           "-- (if $unrollht(C, typeuse) = SUB typeuse'* comptype')*\n----"
         insertedText :=
           "-- (if $unrollht(C, typeuse) = SUB typeuse'* comptype')*\n-- (Typeuse_ok: C |- typeuse : OK)*\n----"
         effect := .narrow
         affectedAuthoritySymbols := ["Subtype_ok2"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Subtype_ok2A"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/issues/2141",
       "https://github.com/WebAssembly/spec/commit/44b03c21317f07500f66bc739553c83dcde445eb"] }

/-- DEV-014: the pinned instantiation clauses force constant-expression
evaluation back to its source state even though the validated constant grammar
contains managed-heap allocation.  The public release initializer threads each
post-expression state and carries its structure/array heaps into final module
allocation; the pinned relations remain available as authority references. -/
def core3InstantiationStateAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-014"
    amendmentId := "AMD-014"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "4.4-execution.modules.spectec"
         sourceSha256 :=
           "9942402b36940c45f9aab76996bc11ffbe6d478e88b1a742bec08e62dce96d17"
         beforeAnchor := "def $evalglobals(z, gt gt'*, expr expr'*) = (z', val val'*)"
         afterAnchor := "-- if (s', a) = $allocglobal(s, gt, val)"
         removedText :=
           "-- Eval_expr: z; expr ~>* z; val\n-- if z = s; f"
         insertedText :=
           "-- Eval_expr: z; expr ~>* z_1; val\n-- if z_1 = s; f"
         effect := .widen
         affectedAuthoritySymbols := ["$evalglobals"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.EvalGlobalsA"] },
       { sourcePath := authoritySource "4.4-execution.modules.spectec"
         sourceSha256 :=
           "9942402b36940c45f9aab76996bc11ffbe6d478e88b1a742bec08e62dce96d17"
         beforeAnchor := "-- if z = s; {MODULE moduleinst_0}"
         afterAnchor := "-- if instr_D* = $concat_"
         removedText :=
           "-- if (z', val_G*) = $evalglobals(z, globaltype*, expr_G*)\n-- (Eval_expr : z'; expr_T ~>* z'; ref_T)*\n-- (Eval_expr : z'; expr_E ~>* z'; ref_E)**\n-- if (s', moduleinst) = $allocmodule(s, module, externaddr*, val_G*, ref_T*, (ref_E*)*)"
         insertedText :=
           "-- if (z_G, val_G*) = $evalglobalsA(z, globaltype*, expr_G*)\n-- if (z_T, ref_T*) = $evalrefexprsA(z_G, expr_T*)\n-- if (z_E, (ref_E*)*) = $evalrefexprlistsA(z_T, (expr_E*)*)\n-- if s_H = $carryconstheap(s, z_E.STORE)\n-- if (s', moduleinst) = $allocmodule(s_H, module, externaddr*, val_G*, ref_T*, (ref_E*)*)"
         effect := .widen
         affectedAuthoritySymbols := ["$instantiate"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.EvalRefExprsA",
            "WasmGemmGnaf.Wasm.Core.Exec.EvalRefExprListsA",
            "WasmGemmGnaf.Wasm.Core.Exec.Store.carryConstHeap",
            "WasmGemmGnaf.Wasm.Core.Exec.InstantiateA"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/9d36019973201a19f9c9ebb0f10828b2fe2374aa/specification/wasm-3.0/4.4-execution.modules.spectec"] }

/-- DEV-015: composing the ordinary recursive-type rule with `_rec2` resets
relative recursive indices for the suffix, while semantic closure later uses
the full original group.  The release rule forbids exactly those rebased
relative declared supertypes; grammar type uses are indices and are unchanged. -/
def core3MixedRecScopeAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-015"
    amendmentId := "AMD-015"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "2.1-validation.types.spectec"
         sourceSha256 :=
           "4b5836e27d39b78a9b29dcdf5be9493abebdaabbcb7f76ef3dfd84b2870c789b"
         beforeAnchor := "rule Rectype_ok/cons:"
         afterAnchor := "rule Rectype_ok/_rec2:"
         removedText :=
           "C |- REC (subtype_1 subtype*) : OK(x)\n-- Subtype_ok: C |- subtype_1 : OK(x)\n-- Rectype_ok: C |- REC subtype* : OK($(x+1))"
         insertedText :=
           "C |- REC (subtype_1 subtype*) : OK(x)\n-- Subtype_ok: C |- subtype_1 : OK(x)\n-- if $no_rebased_rec_supers(REC subtype*) = true\n-- Rectype_ok: C |- REC subtype* : OK($(x+1))"
         effect := .narrow
         affectedAuthoritySymbols := ["Rectype_ok/cons"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.RecType.noRebasedRecSupers",
            "WasmGemmGnaf.Wasm.Core.Rectype_okA",
            "WasmGemmGnaf.Wasm.Core.Validate.checkRectypeOkA"] }]
    upstreamReferences :=
      ["https://github.com/WebAssembly/spec/blob/9d36019973201a19f9c9ebb0f10828b2fe2374aa/specification/wasm-3.0/2.1-validation.types.spectec"] }

/-- DEV-016: the pinned rules' `num_` and `lit_` metavariables already range
over side-conditioned syntax sorts, but Lean's raw `FN` representation also
contains out-of-range constructor terms.  The release selector makes that
implicit sort premise explicit exactly where a result literal is recovered
only through a byte equation. -/
def core3ByteSolvedLiteralAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-016"
    amendmentId := "AMD-016"
    specSection := "4 and 7.1"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "4.3-execution.instructions.spectec"
         sourceSha256 :=
           "faf09ffd37208f3137d37a8b7347ee6b658e9efb166a71ade0375c687fd14fb6"
         beforeAnchor := "rule Step_read/load-num-val:"
         afterAnchor := "rule Step_read/load-pack-oob:"
         removedText :=
           "-- if $nbytes_(nt, c) = $mem(z, x).BYTES[i + ao.OFFSET : $size(nt)/8]"
         insertedText :=
           "-- if $nbytes_(nt, c) = $mem(z, x).BYTES[i + ao.OFFSET : $size(nt)/8]\n-- if c belongs to the side-conditioned syntax sort num_(nt)"
         effect := .narrow
         affectedAuthoritySymbols := ["Step_read/load-num-val"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.ByteSolvedNumWfA"] },
       { sourcePath := authoritySource "4.3-execution.instructions.spectec"
         sourceSha256 :=
           "faf09ffd37208f3137d37a8b7347ee6b658e9efb166a71ade0375c687fd14fb6"
         beforeAnchor := "rule Step_read/array.new_data-num:"
         afterAnchor := "rule Step_read/array.get-null:"
         removedText :=
           "-- if $concatn_(byte, $zbytes_(zt, c)^n, $($zsize(zt)/8)) = $data(z, y).BYTES[i : n * $zsize(zt)/8]"
         insertedText :=
           "-- if $concatn_(byte, $zbytes_(zt, c)^n, $($zsize(zt)/8)) = $data(z, y).BYTES[i : n * $zsize(zt)/8]\n-- if every c belongs to the side-conditioned syntax sort lit_(zt)"
         effect := .narrow
         affectedAuthoritySymbols := ["Step_read/array.new_data-num"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.ByteSolvedLiteralWfA"] },
       { sourcePath := authoritySource "4.3-execution.instructions.spectec"
         sourceSha256 :=
           "faf09ffd37208f3137d37a8b7347ee6b658e9efb166a71ade0375c687fd14fb6"
         beforeAnchor := "rule Step_read/array.init_data-num:"
         afterAnchor := ";; External reference instructions"
         removedText :=
           "-- if $zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]"
         insertedText :=
           "-- if $zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]\n-- if c belongs to the side-conditioned syntax sort lit_(zt)"
         effect := .narrow
         affectedAuthoritySymbols := ["Step_read/array.init_data-num"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.ByteSolvedLiteralWfA"] }]
    upstreamReferences :=
      ["vendor/wasm-spec/specification/wasm-3.0/1.3-syntax.instructions.spectec",
       "vendor/wasm-spec/specification/wasm-3.0/1.1-syntax.values.spectec"] }

/-- DEV-021: the pinned local rules classify initialization state but omit
ordinary value-type validity.  The release relation restores that premise for
both defaultable and nondefaultable locals. -/
def core3LocalValueTypeAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-021"
    amendmentId := "AMD-021"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "2.4-validation.modules.spectec"
         sourceSha256 :=
           "c458e3b91eb6d1a0c2645e5ef1ea54ee7d279562a4c4499ea3e8476b3acbfcfd"
         beforeAnchor := "rule Table_ok:"
         afterAnchor := "rule Func_ok:"
         removedText :=
           "rule Local_ok/set:\n  C |- LOCAL t : SET t\n  -- Defaultable: |- t DEFAULTABLE\n\nrule Local_ok/unset:\n  C |- LOCAL t : UNSET t\n  -- Nondefaultable: |- t NONDEFAULTABLE"
         insertedText :=
           "rule Local_ok/set:\n  C |- LOCAL t : SET t\n  -- Valtype_ok: C |- t : OK\n  -- Defaultable: |- t DEFAULTABLE\n\nrule Local_ok/unset:\n  C |- LOCAL t : UNSET t\n  -- Valtype_ok: C |- t : OK\n  -- Nondefaultable: |- t NONDEFAULTABLE"
         effect := .narrow
         affectedAuthoritySymbols := ["Local_ok/set", "Local_ok/unset"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Local_okA"] }]
    upstreamReferences :=
      ["vendor/wasm-spec/specification/wasm-3.0/2.4-validation.modules.spectec"] }

/-- DEV-022: rolling an in-group `_IDX` reference to `REC i` preserves the
exact outer composite shape already stored at `C.RECS[i]`.  The release
relation adds only those three lookup-indexed shape edges. -/
def core3RecursiveHeapShapeAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-022"
    amendmentId := "AMD-022"
    specSection := "4 and 7.3"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "2.2-validation.subtyping.spectec"
         sourceSha256 :=
           "71ebcb2a53e55b8246c139e70ffbe7f4885c45eb757f8e7138e1563014cd432f"
         beforeAnchor := "rule Heaptype_sub/typeidx-r:"
         afterAnchor := "rule Heaptype_sub/none:"
         removedText :=
           "rule Heaptype_sub/rec:\n  C |- REC i <: typeuse*[j]\n  -- if C.RECS[i] = SUB final? typeuse* ct"
         insertedText :=
           "rule Heaptype_sub/rec:\n  C |- REC i <: typeuse*[j]\n  -- if C.RECS[i] = SUB final? typeuse* ct\n\nrule Heaptype_sub/rec-struct:\n  C |- REC i <: STRUCT\n  -- if C.RECS[i] = SUB final? typeuse* STRUCT fieldtype*\n\nrule Heaptype_sub/rec-array:\n  C |- REC i <: ARRAY\n  -- if C.RECS[i] = SUB final? typeuse* ARRAY fieldtype\n\nrule Heaptype_sub/rec-func:\n  C |- REC i <: FUNC\n  -- if C.RECS[i] = SUB final? typeuse* FUNC t_1* -> t_2*"
         effect := .widen
         affectedAuthoritySymbols :=
           ["Heaptype_sub/rec-struct", "Heaptype_sub/rec-array",
            "Heaptype_sub/rec-func"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Heaptype_subA",
            "WasmGemmGnaf.Wasm.Core.Context.typeuseShapeA",
            "WasmGemmGnaf.Wasm.Core.decHeapSubR"] }]
    upstreamReferences :=
      ["vendor/wasm-spec/specification/wasm-3.0/2.2-validation.subtyping.spectec"] }

/-- DEV-023: `try_table` constructs an administrative handler, but the pinned
rule set neither evaluates that handler's body nor releases a completed trap.
The release relation adds precisely those two administrative edges. -/
def core3HandlerExecutionAuthorityAmendment : AuthorityAmendmentBody :=
  { deviationId := "DEV-023"
    amendmentId := "AMD-023"
    specSection := "4, 7.1, 7.3, and 15"
    pinnedCommit := core3RevisionCommit
    patches :=
      [{ sourcePath := authoritySource "4.3-execution.instructions.spectec"
         sourceSha256 :=
           "faf09ffd37208f3137d37a8b7347ee6b658e9efb166a71ade0375c687fd14fb6"
         beforeAnchor := "rule Step/ctxt-frame:"
         afterAnchor := ";; Polymorphic instructions"
         removedText := ""
         insertedText :=
           "rule Step/ctxt-handler:\n  z; (HANDLER_ n `{catch*} instr*) ~> z'; (HANDLER_ n `{catch*} instr'*)\n  -- Step: z; instr* ~> z'; instr'*"
         effect := .add
         affectedAuthoritySymbols := ["Step/ctxt-handler"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.HandlerAdministrativeRulesFor"] },
       { sourcePath := authoritySource "4.3-execution.instructions.spectec"
         sourceSha256 :=
           "faf09ffd37208f3137d37a8b7347ee6b658e9efb166a71ade0375c687fd14fb6"
         beforeAnchor := "rule Step_pure/trap-frame:"
         afterAnchor := ";; Local instructions"
         removedText := ""
         insertedText :=
           "rule Step_pure/trap-handler:\n  (HANDLER_ n `{catch*} TRAP) ~> TRAP"
         effect := .add
         affectedAuthoritySymbols := ["Step_pure/trap-handler"]
         amendedLeanDeclarations :=
           ["WasmGemmGnaf.Wasm.Core.Exec.HandlerAdministrativeRulesFor"] }]
    upstreamReferences :=
      ["vendor/wasm-spec/specification/wasm-3.0/4.3-execution.instructions.spectec"] }

def core3AuthorityAmendments : List AuthorityAmendmentBody :=
  [ core3InstrSeqAuthorityAmendment
  , core3SignedLebAuthorityAmendment
  , core3PromoteOpcodeAuthorityAmendment
  , core3ExceptionFreeAuthorityAmendment
  , core3CallRefAuthorityAmendment
  , core3BottomSubtypingAuthorityAmendment
  , core3RelaxedDotAddAuthorityAmendment
  , core3SupertypeValidityAuthorityAmendment
  , core3InstantiationStateAuthorityAmendment
  , core3MixedRecScopeAuthorityAmendment
  , core3ByteSolvedLiteralAuthorityAmendment
  , core3LocalValueTypeAuthorityAmendment
  , core3RecursiveHeapShapeAuthorityAmendment
  , core3HandlerExecutionAuthorityAmendment ]

def core3AuthorityAmendmentSet : AuthorityAmendmentSetBody :=
  { vendoredTreeId := VendoredTreeBody.identity core3VendoredTree
    amendments := core3AuthorityAmendments }

theorem core3AuthorityAmendmentIds :
    core3AuthorityAmendments.map AuthorityAmendmentBody.amendmentId =
      ["AMD-005", "AMD-007", "AMD-008", "AMD-009", "AMD-010", "AMD-011",
       "AMD-012", "AMD-013", "AMD-014", "AMD-015", "AMD-016",
       "AMD-021", "AMD-022", "AMD-023"] := rfl

theorem core3AuthorityDeviationIds :
    core3AuthorityAmendments.map AuthorityAmendmentBody.deviationId =
      ["DEV-006", "DEV-007", "DEV-008", "DEV-009", "DEV-010", "DEV-011",
       "DEV-012", "DEV-013", "DEV-014", "DEV-015", "DEV-016",
       "DEV-021", "DEV-022", "DEV-023"] := rfl

theorem core3AuthorityAmendmentIds_nodup :
    (core3AuthorityAmendments.map AuthorityAmendmentBody.amendmentId).Nodup := by
  decide

theorem core3AuthorityDeviationIds_nodup :
    (core3AuthorityAmendments.map AuthorityAmendmentBody.deviationId).Nodup := by
  decide

theorem core3AuthorityAmendmentSet_tree :
    core3AuthorityAmendmentSet.vendoredTreeId =
      VendoredTreeBody.identity core3VendoredTree := rfl

theorem core3AuthorityAmendmentSet_identity_eq_iff
    (s : AuthorityAmendmentSetBody) :
    AuthorityAmendmentSetBody.identity s =
        AuthorityAmendmentSetBody.identity core3AuthorityAmendmentSet ↔
      s = core3AuthorityAmendmentSet :=
  AuthorityAmendmentSetBody.identity_eq_iff

end WasmGemmGnaf.Wasm
