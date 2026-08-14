/-
  Wasm/Core/BinaryGrammar/Expressions.lean --- the recursive part of the
  instruction grammar, and `Bexpr`, for the pinned WebAssembly Core 3.0 front
  end.

  NORMATIVE SOURCE.

      vendor/wasm-spec/specification/wasm-3.0/5.3-binary.instructions.spectec

  SpecTec writes the instruction grammar as a family of extensions of ONE
  nonterminal:

      grammar Binstr/parametric : instr = | 0x00 => UNREACHABLE | ...
      grammar Binstr/block : instr = ... | 0x02 bt:Bblocktype (in:Binstr)* 0x0B => ...
      grammar Binstr/control : instr = ... | 0x08 x:Btagidx => THROW x | ...

  so `Binstr` is the UNION of its fragments.  `BinaryGrammar/Instructions.lean`
  and `BinaryGrammar/Vector.lean` carry the fragments that do not mention
  `Binstr`; this file carries the four alternatives that do -- `BLOCK`, `LOOP`,
  the two forms of `IF`, and `TRY_TABLE` -- and takes the union.  Splitting the
  grammar this way is what keeps the recursive knot down to five constructors
  instead of five hundred; it changes no derivation, because a union of
  relations is what the source's notation means.

  `END` AND `ELSE` ARE PART OF THE GRAMMAR, not of a decoder's control flow.
  Every block form is terminated by the terminal `0x0B`, and the two-branch `IF`
  is separated by `0x05`; both appear literally in the byte sequences below, as
  they do in the source.  `Bexpr` is likewise `(in:Binstr)* 0x0B`, so an
  expression that runs off the end of its input simply has no derivation.
-/
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.Vector
import WasmGemmGnaf.Wasm.Core.BinaryGrammar.InstructionsAmended

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core.Binary

variable [authority : BinaryAuthority]

mutual

/-- `grammar Binstr : instr`, the union of every `Binstr/<fragment>` extension
of the pinned source. -/
inductive Binstr : Bytes → Instr → Prop where
  -- Binstr/block
  /-- `| 0x02 bt:Bblocktype (in:Binstr)* 0x0B => BLOCK bt in*`. -/
  -- core-opcode: 0x02 BLOCK
  | block (bbt bin : Bytes) (bt : BlockType) (ins : List Instr) :
      Bblocktype bbt bt → Binstrs bin ins →
      Binstr (tb 0x02 :: (bbt ++ bin ++ [tb 0x0B])) (.block bt (InstrSeq.ofList ins))
  /-- `| 0x03 bt:Bblocktype (in:Binstr)* 0x0B => LOOP bt in*`. -/
  -- core-opcode: 0x03 LOOP
  | loop (bbt bin : Bytes) (bt : BlockType) (ins : List Instr) :
      Bblocktype bbt bt → Binstrs bin ins →
      Binstr (tb 0x03 :: (bbt ++ bin ++ [tb 0x0B])) (.loop bt (InstrSeq.ofList ins))
  /-- `| 0x04 bt:Bblocktype (in:Binstr)* 0x0B => IF bt in* ELSE eps`. -/
  -- core-opcode: 0x04 IF
  | ifThen (bbt bin : Bytes) (bt : BlockType) (ins : List Instr) :
      Bblocktype bbt bt → Binstrs bin ins →
      Binstr (tb 0x04 :: (bbt ++ bin ++ [tb 0x0B]))
        (.ifElse bt (InstrSeq.ofList ins) .nil)
  /-- `| 0x04 bt:Bblocktype (in_1:Binstr)* 0x05 (in_2:Binstr)* 0x0B
        => IF bt in_1* ELSE in_2*`.

  This alternative spans two lines in the pinned source, so `xtask core`'s
  extractor -- which reads one production per line -- folds it into the same
  checklist entry as the `ELSE eps` form.  It is a distinct production and is
  transcribed as one. -/
  -- core-opcode: 0x04 IF
  | ifElse (bbt b₁ b₂ : Bytes) (bt : BlockType) (ins₁ ins₂ : List Instr) :
      Bblocktype bbt bt → Binstrs b₁ ins₁ → Binstrs b₂ ins₂ →
      Binstr (tb 0x04 :: (bbt ++ b₁ ++ [tb 0x05] ++ b₂ ++ [tb 0x0B]))
        (.ifElse bt (InstrSeq.ofList ins₁) (InstrSeq.ofList ins₂))
  -- Binstr/control
  /-- `| 0x1F bt:Bblocktype c*:Blist(Bcatch) (in:Binstr)* 0x0B
        => TRY_TABLE bt c* in*`. -/
  -- core-opcode: 0x1F TRY_TABLE
  | tryTable (bbt bc bin : Bytes) (bt : BlockType) (cs : List_ Catch)
      (ins : List Instr) :
      Bblocktype bbt bt → Blist Bcatch bc cs.val → Binstrs bin ins →
      Binstr (tb 0x1F :: (bbt ++ bc ++ bin ++ [tb 0x0B]))
        (.tryTable bt cs (InstrSeq.ofList ins))
  -- The fragments that do not mention `Binstr`, taken as they stand.
  | ofParametric (bs : Bytes) (i : Instr) : BinstrParametric bs i → Binstr bs i
  | ofControl (bs : Bytes) (i : Instr) : BinstrControlFor bs i → Binstr bs i
  | ofLocal (bs : Bytes) (i : Instr) : BinstrLocal bs i → Binstr bs i
  | ofGlobal (bs : Bytes) (i : Instr) : BinstrGlobal bs i → Binstr bs i
  | ofTable (bs : Bytes) (i : Instr) : BinstrTable bs i → Binstr bs i
  | ofMemory (bs : Bytes) (i : Instr) : BinstrMemory bs i → Binstr bs i
  | ofRef (bs : Bytes) (i : Instr) : BinstrRef bs i → Binstr bs i
  | ofStruct (bs : Bytes) (i : Instr) : BinstrStruct bs i → Binstr bs i
  | ofArray (bs : Bytes) (i : Instr) : BinstrArray bs i → Binstr bs i
  | ofCast (bs : Bytes) (i : Instr) : BinstrCast bs i → Binstr bs i
  | ofExtern (bs : Bytes) (i : Instr) : BinstrExtern bs i → Binstr bs i
  | ofI31 (bs : Bytes) (i : Instr) : BinstrI31 bs i → Binstr bs i
  | ofNum (bs : Bytes) (i : Instr) : BinstrNumFor bs i → Binstr bs i
  | ofVecMem (bs : Bytes) (i : Instr) : BinstrVecMem bs i → Binstr bs i
  | ofVecRel (bs : Bytes) (i : Instr) : BinstrVecRel bs i → Binstr bs i
  | ofVecV128 (bs : Bytes) (i : Instr) : BinstrVecV128 bs i → Binstr bs i
  | ofVecInt8And16 (bs : Bytes) (i : Instr) : BinstrVecInt8And16 bs i → Binstr bs i
  | ofVecInt32And64 (bs : Bytes) (i : Instr) :
      BinstrVecInt32And64For bs i → Binstr bs i
  | ofVecFloat (bs : Bytes) (i : Instr) : BinstrVecFloat bs i → Binstr bs i

/-- `(in:Binstr)*`: the Kleene star of `Binstr`.  It has to be its own inductive
rather than an instance of `Star`, because `Star` is a parameter-level
abbreviation and cannot occur in the recursive knot. -/
inductive Binstrs : Bytes → List Instr → Prop where
  | nil : Binstrs [] []
  | cons (b bs : Bytes) (i : Instr) (is : List Instr) :
      Binstr b i → Binstrs bs is → Binstrs (b ++ bs) (i :: is)

end

/-- `grammar Bexpr : expr = | (in:Binstr)* 0x0B => in*`. -/
inductive Bexpr : Bytes → Expr → Prop where
  | mk (bs : Bytes) (ins : List Instr) :
      Binstrs bs ins → Bexpr (bs ++ [tb 0x0B]) (InstrSeq.ofList ins)

/-- The explicit byte-identical pinned instruction relation. -/
abbrev BinstrPinned := @Binstr pinnedBinaryAuthority

/-- The exact AMD-007/008/010/012 instruction relation. -/
abbrev BinstrA := @Binstr amendedBinaryAuthority

/-- The explicit byte-identical pinned expression relation. -/
abbrev BexprPinned := @Bexpr pinnedBinaryAuthority

/-- The exact AMD-007/008/010/012 expression relation. -/
abbrev BexprA := @Bexpr amendedBinaryAuthority

end WasmGemmGnaf.Wasm.Core.Binary
