/-
  Wasm/Core/DecodeModules.lean --- the executable decoder for
  `5.4-binary.modules.spectec`, proved sound against
  `Wasm/Core/BinaryGrammar/Modules.lean`.

  THE FOUR THINGS THE AUDIT NAMED, AND WHERE THEY ARE HERE:

  * OPTIONAL SECTIONS.  `decSection` returns the empty list and consumes nothing
    when the leading byte is not the section id, which is `Bsection.absent`; a
    present but empty section is a different byte sequence and decodes through
    `Bsection.present`.

  * CUSTOM SECTIONS BETWEEN ANY TWO SECTIONS.  `decCustoms` consumes a maximal
    run of `0x00` sections and is invoked at all fourteen positions the pinned
    production writes.  A custom section's payload must still begin with a valid
    UTF-8 `Bname`, which is what `Bcustom` demands.

  * THE FUNCTION / CODE SPLIT.  The function section carries `typeidx*`, the
    code section carries `(local*, expr)*`, and `decModule` pairs them with
    `List.zipWith` after checking the two lists have equal length -- the
    starred side condition of the pinned production.

  * THE DATA COUNT SECTION.  Section `12` is decoded, and both of its side
    conditions are CHECKED rather than assumed: the count must equal the number
    of data segments, and it must be present whenever any function body mentions
    a data index (`dataIdxFuncs`).

  COMPRESSED LOCALS are `decLocals`: a `Bu32` run length and one value type,
  expanded by `List.replicate`, with the pinned bound on the concatenation.

  WHAT IS PROVED.  `decModule_sound : decModule bs = .ok m -> Bmodule bs m`.
  Completeness is NOT proved here and is NOT claimed; see the report.
-/
import WasmGemmGnaf.Wasm.Core.DecodeInstructions

set_option autoImplicit false
set_option maxRecDepth 20000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Sections -/

/-- `grammar Bsection_(N, BX)`.  The inner grammar must consume the whole
payload, which is what `len = ||BX||` says. -/
def decSection {α : Type} (N : Nat) (inner : Bytes → Except Fault (List α × Bytes))
    (bs : Bytes) : Except Fault (List α × Bytes) :=
  match bs with
  | [] => .ok ([], [])
  | b :: r =>
      if b.val = N then
        (match decU32 r with
         | .error e => .error e
         | .ok (len, r₁) =>
             if (r₁.take len.val).length = len.val then
               (match inner (r₁.take len.val) with
                | .error e => .error e
                | .ok (xs, rest) =>
                    if rest.isEmpty then .ok (xs, r₁.drop len.val)
                    else .error .section_)
             else .error .section_)
      else .ok ([], b :: r)

theorem decSection_sound {α : Type} {G : Bytes → List α → Prop}
    {inner : Bytes → Except Fault (List α × Bytes)} (hI : Sound G inner) (N : Nat)
    (hN : N < 0x100) : Sound (Bsection N G) (decSection N inner) := by
  intro bs xs r h
  cases bs with
  | nil =>
      rw [decSection] at h
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      exact ⟨[], by simp [← hr], by rw [← hv]; exact Bsection.absent⟩
  | cons b bs =>
      rw [decSection] at h
      split at h
      · rename_i hb
        split at h
        · cases h
        · rename_i len r₁ hlen
          split at h
          · rename_i hlen'
            split at h
            · cases h
            · rename_i ys rest hinner
              split at h
              · rename_i hempty
                obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
                obtain ⟨blen, hblen, hdlen⟩ := decU32_sound bs len r₁ hlen
                obtain ⟨payload, hpay, hG⟩ := hI (r₁.take len.val) ys rest hinner
                have hrest : rest = [] := by
                  cases rest with
                  | nil => rfl
                  | cons _ _ => simp at hempty
                have hpay' : r₁.take len.val = payload := by
                  rw [hpay, hrest]; simp
                refine ⟨b :: (blen ++ r₁.take len.val), ?_, ?_⟩
                · rw [hblen, ← hr]
                  simp only [List.cons_append, List.append_assoc]
                  rw [List.take_append_drop]
                · rw [byte_eq_tb hN hb, ← hv, hpay']
                  refine Bsection.present blen payload len ys hdlen (hpay' ▸ hG) ?_
                  rw [← hpay', hlen']
              · cases h
          · cases h
      · obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨[], by simp [← hr], by rw [← hv]; exact Bsection.absent⟩

/-! ## Custom sections -/

/-- `grammar Bcustom : ()*`: a name followed by arbitrary bytes. -/
def decCustom (payload : Bytes) : Except Fault (List Unit × Bytes) :=
  match decName payload with
  | .error e => .error e
  | .ok (_, rest) => .ok ([()], rest)

/-- A maximal run of custom sections; returns what is left. -/
def decCustoms : Nat → Bytes → Except Fault Bytes
  | 0, bs => .ok bs
  | n + 1, bs =>
      match bs with
      | [] => .ok bs
      | b :: r =>
          if b.val = 0x00 then
            (match decU32 r with
             | .error e => .error e
             | .ok (len, r₁) =>
                 if (r₁.take len.val).length = len.val then
                   (match decName (r₁.take len.val) with
                    | .error e => .error e
                    | .ok (_nm, _rest) => decCustoms n (r₁.drop len.val))
                 else .error .section_)
          else .ok bs

theorem decCustoms_sound : ∀ (n : Nat) (bs r : Bytes), decCustoms n bs = .ok r →
    ∃ c us, bs = c ++ r ∧ Star Bcustomsec c us := by
  intro n
  induction n with
  | zero =>
      intro bs r h
      rw [decCustoms] at h
      have hbr : bs = r := Except.ok.inj h
      exact ⟨[], [], by simp [hbr], ⟨0, Rep.nil⟩⟩
  | succ n ih =>
      intro bs r h
      cases bs with
      | nil =>
          rw [decCustoms] at h
          have hbr : ([] : Bytes) = r := Except.ok.inj h
          exact ⟨[], [], by simp [← hbr], ⟨0, Rep.nil⟩⟩
      | cons b bs =>
          rw [decCustoms] at h
          split at h
          · rename_i hb
            split at h
            · cases h
            · rename_i len r₁ hlen
              split at h
              · rename_i hlen'
                split at h
                · cases h
                · rename_i nm rest hnm
                  obtain ⟨c, us, hc, hus⟩ := ih (r₁.drop len.val) r h
                  obtain ⟨blen, hblen, hdlen⟩ := decU32_sound bs len r₁ hlen
                  obtain ⟨bn, hbn, hdn⟩ := decName_sound (r₁.take len.val) nm rest hnm
                  obtain ⟨k, hk⟩ := hus
                  refine ⟨b :: (blen ++ r₁.take len.val) ++ c, () :: us, ?_, k + 1, ?_⟩
                  · have hsplit : List.take len.val r₁ ++ (c ++ r) = r₁ := by
                      rw [← hc, List.take_append_drop]
                    rw [hblen]
                    simp only [List.cons_append, List.append_assoc]
                    rw [hsplit]
                  · refine Rep.cons (b :: (blen ++ r₁.take len.val)) () c us k ?_ hk
                    refine Bcustomsec.mk _ [()] ?_
                    rw [byte_eq_tb (by decide) hb]
                    refine Bsection.present blen (r₁.take len.val) len [()] hdlen ?_ hlen'.symm
                    rw [hbn]
                    exact Bcustom.mk bn rest nm rest hdn (Star_Bbyte_self rest)
              · cases h
          · have hbr : b :: bs = r := Except.ok.inj h
            exact ⟨[], [], by simp [hbr], ⟨0, Rep.nil⟩⟩

/-! ## Section payloads -/

/-- `grammar Btype : type`. -/
def decType (bs : Bytes) : Except Fault (TypeDef × Bytes) :=
  match decRectype bs with
  | .error e => .error e
  | .ok (qt, r) => .ok ({ rectype := qt }, r)

theorem decType_sound : Sound Btype decType := by
  intro bs t r h
  rw [decType] at h
  split at h
  · cases h
  · rename_i qt r' hq
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := decRectype_sound bs qt r' hq
    exact ⟨b, by rw [hb, hr], by rw [← hv]; exact Btype.mk b qt hd⟩

/-- `grammar Bimport : import`. -/
def decImport (bs : Bytes) : Except Fault (Import × Bytes) :=
  match decName bs with
  | .error e => .error e
  | .ok (nm₁, r₁) =>
      match decName r₁ with
      | .error e => .error e
      | .ok (nm₂, r₂) =>
          match decExterntype r₂ with
          | .error e => .error e
          | .ok (xt, r₃) =>
              .ok ({ moduleName := nm₁, itemName := nm₂, externtype := xt }, r₃)

theorem decImport_sound : Sound Bimport decImport := by
  intro bs im r h
  rw [decImport] at h
  split at h
  · cases h
  · rename_i nm₁ r₁ h₁
    split at h
    · cases h
    · rename_i nm₂ r₂ h₂
      split at h
      · cases h
      · rename_i xt r₃ h₃
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨b₁, hb₁, hd₁⟩ := decName_sound bs nm₁ r₁ h₁
        obtain ⟨b₂, hb₂, hd₂⟩ := decName_sound r₁ nm₂ r₂ h₂
        obtain ⟨b₃, hb₃, hd₃⟩ := decExterntype_sound r₂ xt r₃ h₃
        refine ⟨b₁ ++ b₂ ++ b₃, by rw [hb₁, hb₂, hb₃, hr]; simp, ?_⟩
        rw [← hv]
        exact Bimport.mk b₁ b₂ b₃ nm₁ nm₂ xt hd₁ hd₂ hd₃

/-- `grammar Btable : table`.  The `0x40 0x00` form carries an explicit
initialiser; otherwise the table type's own element type supplies
`REF.NULL ht`. -/
def decTable (d : Nat) (bs : Bytes) : Except Fault (Table × Bytes) :=
  match bs with
  | [] => .error .eof
  | b :: r =>
      if b.val = 0x40 then
        (match expectByte 0x00 r with
         | .error e => .error e
         | .ok r₀ =>
             match decTabletype r₀ with
             | .error e => .error e
             | .ok (tt, r₁) =>
                 match decExpr d r₁ with
                 | .error e => .error e
                 | .ok (e, r₂) => .ok ({ tabletype := tt, init := e }, r₂))
      else
        (match decTabletype (b :: r) with
         | .error e => .error e
         | .ok (tt, r₁) =>
             match tt.elem with
             | .ref _ ht => .ok ({ tabletype := tt, init := .cons (.refNull ht) .nil }, r₁))

theorem decTable_sound (d : Nat) : Sound Btable (decTable d) := by
  intro bs tab r h
  cases bs with
  | nil => cases h
  | cons b bs =>
      rw [decTable] at h
      split at h
      · rename_i hb
        split at h
        · cases h
        · rename_i r₀ hr₀
          split at h
          · cases h
          · rename_i tt r₁ ht
            split at h
            · cases h
            · rename_i e r₂ he
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨bt, hbt, hdt⟩ := decTabletype_sound r₀ tt r₁ ht
              obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₁ e r₂ he
              have h0 := expectByte_ok (by decide : (0x00 : Nat) < 0x100) hr₀
              refine ⟨tb 0x40 :: tb 0x00 :: (bt ++ be), ?_, ?_⟩
              · rw [byte_eq_tb (by decide) hb, h0, hbt, hbe, hr]; simp
              · rw [← hv]; exact Btable.withInit bt be tt e hdt hde
      · split at h
        · cases h
        · rename_i tt r₁ ht
          obtain ⟨bt, hbt, hdt⟩ := decTabletype_sound (b :: bs) tt r₁ ht
          revert h
          match hte : tt.elem with
          | .ref nul ht =>
              intro h
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              refine ⟨bt, by rw [hbt, hr], ?_⟩
              rw [← hv]
              exact Btable.shorthand bt tt nul ht hdt hte

/-- `grammar Bmem : mem`. -/
def decMem (bs : Bytes) : Except Fault (Mem × Bytes) :=
  match decMemtype bs with
  | .error e => .error e
  | .ok (mt, r) => .ok ({ memtype := mt }, r)

theorem decMem_sound : Sound Bmem decMem := by
  intro bs m r h
  rw [decMem] at h
  split at h
  · cases h
  · rename_i mt r' hm
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := decMemtype_sound bs mt r' hm
    exact ⟨b, by rw [hb, hr], by rw [← hv]; exact Bmem.mk b mt hd⟩

/-- `grammar Btag : tag`. -/
def decTag (bs : Bytes) : Except Fault (Tag × Bytes) :=
  match decTagtype bs with
  | .error e => .error e
  | .ok (jt, r) => .ok ({ tagtype := jt }, r)

theorem decTag_sound : Sound Btag decTag := by
  intro bs t r h
  rw [decTag] at h
  split at h
  · cases h
  · rename_i jt r' hj
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := decTagtype_sound bs jt r' hj
    exact ⟨b, by rw [hb, hr], by rw [← hv]; exact Btag.mk b jt hd⟩

/-- `grammar Bglobal : global`. -/
def decGlobal (d : Nat) (bs : Bytes) : Except Fault (Global × Bytes) :=
  match decGlobaltype bs with
  | .error e => .error e
  | .ok (gt, r₁) =>
      match decExpr d r₁ with
      | .error e => .error e
      | .ok (e, r₂) => .ok ({ globaltype := gt, init := e }, r₂)

theorem decGlobal_sound (d : Nat) : Sound Bglobal (decGlobal d) := by
  intro bs g r h
  rw [decGlobal] at h
  split at h
  · cases h
  · rename_i gt r₁ hg
    split at h
    · cases h
    · rename_i e r₂ he
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨bg, hbg, hdg⟩ := decGlobaltype_sound bs gt r₁ hg
      obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₁ e r₂ he
      refine ⟨bg ++ be, by rw [hbg, hbe, hr]; simp, ?_⟩
      rw [← hv]
      exact Bglobal.mk bg be gt e hdg hde

/-- `grammar Bexport : export`. -/
def decExport (bs : Bytes) : Except Fault (Export × Bytes) :=
  match decName bs with
  | .error e => .error e
  | .ok (nm, r₁) =>
      match decExternidx r₁ with
      | .error e => .error e
      | .ok (xx, r₂) => .ok ({ name := nm, externidx := xx }, r₂)

theorem decExport_sound : Sound Bexport decExport := by
  intro bs ex r h
  rw [decExport] at h
  split at h
  · cases h
  · rename_i nm r₁ hn
    split at h
    · cases h
    · rename_i xx r₂ hx
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨bn, hbn, hdn⟩ := decName_sound bs nm r₁ hn
      obtain ⟨bx, hbx, hdx⟩ := decExternidx_sound r₁ xx r₂ hx
      refine ⟨bn ++ bx, by rw [hbn, hbx, hr]; simp, ?_⟩
      rw [← hv]
      exact Bexport.mk bn bx nm xx hdn hdx

/-- `grammar Bstart : start*`. -/
def decStart (bs : Bytes) : Except Fault (List Start × Bytes) :=
  match decIdx bs with
  | .error e => .error e
  | .ok (x, r) => .ok ([{ funcidx := x }], r)

theorem decStart_sound : Sound Bstart decStart := by
  intro bs ss r h
  rw [decStart] at h
  split at h
  · cases h
  · rename_i x r' hx
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := decIdx_sound bs x r' hx
    exact ⟨b, by rw [hb, hr], by rw [← hv]; exact Bstart.mk b x hd⟩

/-- `grammar Bdatacnt : u32*`. -/
def decDatacnt (bs : Bytes) : Except Fault (List U32 × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (n, r) => .ok ([n], r)

theorem decDatacnt_sound : Sound Bdatacnt decDatacnt := by
  intro bs ns r h
  rw [decDatacnt] at h
  split at h
  · cases h
  · rename_i n r' hn
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨b, hb, hd⟩ := decU32_sound bs n r' hn
    exact ⟨b, by rw [hb, hr], by rw [← hv]; exact Bdatacnt.mk b n hd⟩

/-- `grammar Belemkind : reftype = | 0x00 => REF NULL FUNC`. -/
def decElemkind (bs : Bytes) : Except Fault (RefType × Bytes) :=
  match expectByte 0x00 bs with
  | .error e => .error e
  | .ok r => .ok (.ref (some .null) (.abs .func), r)

theorem decElemkind_sound : Sound Belemkind decElemkind := by
  intro bs rt r h
  rw [decElemkind] at h
  split at h
  · cases h
  · rename_i r' hr'
    obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
    have h0 := expectByte_ok (by decide : (0x00 : Nat) < 0x100) hr'
    exact ⟨[tb 0x00], by simp [h0, hr], by rw [← hv]; exact Belemkind.funcref⟩

/-- `grammar Belem : elem`, all eight tag forms. -/
def decElem (d : Nat) (bs : Bytes) : Except Fault (Elem × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (t, r) =>
      match t.val with
      | 0 =>
          (match decExpr d r with
           | .error e => .error e
           | .ok (e, r₁) =>
               match decList decIdx r₁ with
               | .error e => .error e
               | .ok (ys, r₂) =>
                   .ok ({ reftype := .ref none (.abs .func), init := refFuncExprs ys,
                          mode := .active ⟨0, two_pow_pos 32⟩ e }, r₂))
      | 1 =>
          (match decElemkind r with
           | .error e => .error e
           | .ok (rt, r₁) =>
               match decList decIdx r₁ with
               | .error e => .error e
               | .ok (ys, r₂) =>
                   .ok ({ reftype := rt, init := refFuncExprs ys, mode := .passive }, r₂))
      | 2 =>
          (match decIdx r with
           | .error e => .error e
           | .ok (x, r₁) =>
               match decExpr d r₁ with
               | .error e => .error e
               | .ok (e, r₂) =>
                   match decElemkind r₂ with
                   | .error e => .error e
                   | .ok (rt, r₃) =>
                       match decList decIdx r₃ with
                       | .error e => .error e
                       | .ok (ys, r₄) =>
                           .ok ({ reftype := rt, init := refFuncExprs ys,
                                  mode := .active x e }, r₄))
      | 3 =>
          (match decElemkind r with
           | .error e => .error e
           | .ok (rt, r₁) =>
               match decList decIdx r₁ with
               | .error e => .error e
               | .ok (ys, r₂) =>
                   .ok ({ reftype := rt, init := refFuncExprs ys, mode := .declare }, r₂))
      | 4 =>
          (match decExpr d r with
           | .error e => .error e
           | .ok (e, r₁) =>
               match decList (decExpr d) r₁ with
               | .error e => .error e
               | .ok (es, r₂) =>
                   .ok ({ reftype := .ref (some .null) (.abs .func), init := es,
                          mode := .active ⟨0, two_pow_pos 32⟩ e }, r₂))
      | 5 =>
          (match decReftype r with
           | .error e => .error e
           | .ok (rt, r₁) =>
               match decList (decExpr d) r₁ with
               | .error e => .error e
               | .ok (es, r₂) => .ok ({ reftype := rt, init := es, mode := .passive }, r₂))
      | 6 =>
          (match decIdx r with
           | .error e => .error e
           | .ok (x, r₁) =>
               match decExpr d r₁ with
               | .error e => .error e
               | .ok (e, r₂) =>
                   match decList (decExpr d) r₂ with
                   | .error e => .error e
                   | .ok (es, r₃) =>
                       .ok ({ reftype := .ref (some .null) (.abs .func), init := es,
                              mode := .active x e }, r₃))
      | 7 =>
          (match decReftype r with
           | .error e => .error e
           | .ok (rt, r₁) =>
               match decList (decExpr d) r₁ with
               | .error e => .error e
               | .ok (es, r₂) => .ok ({ reftype := rt, init := es, mode := .declare }, r₂))
      | _ => Except.error Fault.opcode

/-- `grammar Bdata : data`. -/
def decData (d : Nat) (bs : Bytes) : Except Fault (Data × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (t, r) =>
      match t.val with
      | 0 =>
          (match decExpr d r with
           | .error e => .error e
           | .ok (e, r₁) =>
               match decList readByte r₁ with
               | .error e => .error e
               | .ok (bl, r₂) =>
                   .ok ({ bytes := bl, mode := .active ⟨0, two_pow_pos 32⟩ e }, r₂))
      | 1 =>
          (match decList readByte r with
           | .error e => .error e
           | .ok (bl, r₁) => .ok ({ bytes := bl, mode := .passive }, r₁))
      | 2 =>
          (match decIdx r with
           | .error e => .error e
           | .ok (x, r₁) =>
               match decExpr d r₁ with
               | .error e => .error e
               | .ok (e, r₂) =>
                   match decList readByte r₂ with
                   | .error e => .error e
                   | .ok (bl, r₃) => .ok ({ bytes := bl, mode := .active x e }, r₃))
      | _ => Except.error Fault.opcode

/-! ## Code -/

/-- `grammar Blocals : local*`: a run length and one value type. -/
def decLocals (bs : Bytes) : Except Fault (List Local × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (n, r₁) =>
      match decValtype r₁ with
      | .error e => .error e
      | .ok (t, r₂) => .ok (List.replicate n.val { valtype := t }, r₂)

theorem decLocals_sound : Sound Blocals decLocals := by
  intro bs ls r h
  rw [decLocals] at h
  split at h
  · cases h
  · rename_i n r₁ hn
    split at h
    · cases h
    · rename_i t r₂ ht
      obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨bn, hbn, hdn⟩ := decU32_sound bs n r₁ hn
      obtain ⟨bt, hbt, hdt⟩ := decValtype_sound r₁ t r₂ ht
      refine ⟨bn ++ bt, by rw [hbn, hbt, hr]; simp, ?_⟩
      rw [← hv]
      exact Blocals.mk bn bt n t hdn hdt

/-- `grammar Bfunc : code`. -/
def decFunc (d : Nat) (bs : Bytes) : Except Fault (Code × Bytes) :=
  match decList decLocals bs with
  | .error e => .error e
  | .ok (locss, r₁) =>
      if locss.flatten.length < 2 ^ 32 then
        (match decExpr d r₁ with
         | .error e => .error e
         | .ok (e, r₂) => .ok ((locss.flatten, e), r₂))
      else .error .side

theorem decFunc_sound (d : Nat) : Sound Bfunc (decFunc d) := by
  intro bs c r h
  rw [decFunc] at h
  split at h
  · cases h
  · rename_i locss r₁ hl
    split at h
    · rename_i hlen
      split at h
      · cases h
      · rename_i e r₂ he
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨bl, hbl, hdl⟩ := decList_sound decLocals_sound bs locss r₁ hl
        obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₁ e r₂ he
        refine ⟨bl ++ be, by rw [hbl, hbe, hr]; simp, ?_⟩
        rw [← hv]
        exact Bfunc.mk bl be locss e hdl hde hlen
    · cases h

/-- `grammar Bcode : code = | len:Bu32 code:Bfunc => code  -- if len = ||Bfunc||`. -/
def decCode (d : Nat) (bs : Bytes) : Except Fault (Code × Bytes) :=
  match decU32 bs with
  | .error e => .error e
  | .ok (len, r₁) =>
      if (r₁.take len.val).length = len.val then
        (match decFunc d (r₁.take len.val) with
         | .error e => .error e
         | .ok (c, rest) =>
             if rest.isEmpty then .ok (c, r₁.drop len.val) else .error .section_)
      else .error .section_

theorem decCode_sound (d : Nat) : Sound Bcode (decCode d) := by
  intro bs c r h
  rw [decCode] at h
  split at h
  · cases h
  · rename_i len r₁ hlen
    split at h
    · rename_i hlen'
      split at h
      · cases h
      · rename_i c' rest hc
        split at h
        · rename_i hempty
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨blen, hblen, hdlen⟩ := decU32_sound bs len r₁ hlen
          obtain ⟨bf, hbf, hdf⟩ := decFunc_sound d (r₁.take len.val) c' rest hc
          have hrest : rest = [] := by
            cases rest with
            | nil => rfl
            | cons _ _ => simp at hempty
          have hbf' : r₁.take len.val = bf := by rw [hbf, hrest]; simp
          refine ⟨blen ++ r₁.take len.val, ?_, ?_⟩
          · rw [hblen, ← hr, List.append_assoc, List.take_append_drop]
          · rw [← hv, hbf']
            exact Bcode.mk blen bf len c' hdlen (hbf' ▸ hdf) (by rw [← hbf', hlen'])
        · cases h
    · cases h


/-! ## Element and data segments -/

theorem decElem_sound (d : Nat) : Sound Belem (decElem d) := by
  intro bs el r h
  rw [decElem] at h
  split at h
  · cases h
  · rename_i t r₀ ht
    obtain ⟨bt, hbt, hdt⟩ := decU32_sound bs t r₀ ht
    split at h
    · rename_i hk
      have hlit : Bu32lit 0 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i e r₁ he
        split at h
        · cases h
        · rename_i ys r₂ hys
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₀ e r₁ he
          obtain ⟨by', hby, hdy⟩ := decList_sound decIdx_sound r₁ ys r₂ hys
          refine ⟨bt ++ be ++ by', by rw [hbt, hbe, hby, hr]; simp, ?_⟩
          rw [← hv]
          exact Belem.activeFuncrefZero bt be by' e ys ⟨0, two_pow_pos 32⟩ hlit hde hdy rfl
    · rename_i hk
      have hlit : Bu32lit 1 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i rt r₁ hrt
        split at h
        · cases h
        · rename_i ys r₂ hys
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bk, hbk, hdk⟩ := decElemkind_sound r₀ rt r₁ hrt
          obtain ⟨by', hby, hdy⟩ := decList_sound decIdx_sound r₁ ys r₂ hys
          refine ⟨bt ++ bk ++ by', by rw [hbt, hbk, hby, hr]; simp, ?_⟩
          rw [← hv]
          exact Belem.passiveFuncref bt bk by' rt ys hlit hdk hdy
    · rename_i hk
      have hlit : Bu32lit 2 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i x r₁ hx
        split at h
        · cases h
        · rename_i e r₂ he
          split at h
          · cases h
          · rename_i rt r₃ hrt
            split at h
            · cases h
            · rename_i ys r₄ hys
              obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨bx, hbx, hdx⟩ := decIdx_sound r₀ x r₁ hx
              obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₁ e r₂ he
              obtain ⟨bk, hbk, hdk⟩ := decElemkind_sound r₂ rt r₃ hrt
              obtain ⟨by', hby, hdy⟩ := decList_sound decIdx_sound r₃ ys r₄ hys
              refine ⟨bt ++ bx ++ be ++ bk ++ by',
                by rw [hbt, hbx, hbe, hbk, hby, hr]; simp, ?_⟩
              rw [← hv]
              exact Belem.activeFuncref bt bx be bk by' x e rt ys hlit hdx hde hdk hdy
    · rename_i hk
      have hlit : Bu32lit 3 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i rt r₁ hrt
        split at h
        · cases h
        · rename_i ys r₂ hys
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨bk, hbk, hdk⟩ := decElemkind_sound r₀ rt r₁ hrt
          obtain ⟨by', hby, hdy⟩ := decList_sound decIdx_sound r₁ ys r₂ hys
          refine ⟨bt ++ bk ++ by', by rw [hbt, hbk, hby, hr]; simp, ?_⟩
          rw [← hv]
          exact Belem.declareFuncref bt bk by' rt ys hlit hdk hdy
    · rename_i hk
      have hlit : Bu32lit 4 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i e r₁ he
        split at h
        · cases h
        · rename_i es r₂ hes
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₀ e r₁ he
          obtain ⟨bl, hbl, hdl⟩ := decList_sound (decExpr_sound d) r₁ es r₂ hes
          refine ⟨bt ++ be ++ bl, by rw [hbt, hbe, hbl, hr]; simp, ?_⟩
          rw [← hv]
          exact Belem.activeExprZero bt be bl e es ⟨0, two_pow_pos 32⟩ hlit hde hdl rfl
    · rename_i hk
      have hlit : Bu32lit 5 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i rt r₁ hrt
        split at h
        · cases h
        · rename_i es r₂ hes
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨br, hbr, hdr⟩ := decReftype_sound r₀ rt r₁ hrt
          obtain ⟨bl, hbl, hdl⟩ := decList_sound (decExpr_sound d) r₁ es r₂ hes
          refine ⟨bt ++ br ++ bl, by rw [hbt, hbr, hbl, hr]; simp, ?_⟩
          rw [← hv]
          exact Belem.passiveExpr bt br bl rt es hlit hdr hdl
    · rename_i hk
      have hlit : Bu32lit 6 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i x r₁ hx
        split at h
        · cases h
        · rename_i e r₂ he
          split at h
          · cases h
          · rename_i es r₃ hes
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bx, hbx, hdx⟩ := decIdx_sound r₀ x r₁ hx
            obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₁ e r₂ he
            obtain ⟨bl, hbl, hdl⟩ := decList_sound (decExpr_sound d) r₂ es r₃ hes
            refine ⟨bt ++ bx ++ be ++ bl, by rw [hbt, hbx, hbe, hbl, hr]; simp, ?_⟩
            rw [← hv]
            exact Belem.activeExpr bt bx be bl x e es hlit hdx hde hdl
    · rename_i hk
      have hlit : Bu32lit 7 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i rt r₁ hrt
        split at h
        · cases h
        · rename_i es r₂ hes
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨br, hbr, hdr⟩ := decReftype_sound r₀ rt r₁ hrt
          obtain ⟨bl, hbl, hdl⟩ := decList_sound (decExpr_sound d) r₁ es r₂ hes
          refine ⟨bt ++ br ++ bl, by rw [hbt, hbr, hbl, hr]; simp, ?_⟩
          rw [← hv]
          exact Belem.declareExpr bt br bl rt es hlit hdr hdl
    · cases h

theorem decData_sound (d : Nat) : Sound Bdata (decData d) := by
  intro bs da r h
  rw [decData] at h
  split at h
  · cases h
  · rename_i t r₀ ht
    obtain ⟨bt, hbt, hdt⟩ := decU32_sound bs t r₀ ht
    split at h
    · rename_i hk
      have hlit : Bu32lit 0 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i e r₁ he
        split at h
        · cases h
        · rename_i bl r₂ hbl
          obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
          obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₀ e r₁ he
          obtain ⟨bb, hbb, hdb⟩ := decList_sound readByte_sound r₁ bl r₂ hbl
          refine ⟨bt ++ be ++ bb, by rw [hbt, hbe, hbb, hr]; simp, ?_⟩
          rw [← hv]
          exact Bdata.activeZero bt be bb e bl ⟨0, two_pow_pos 32⟩ hlit hde hdb rfl
    · rename_i hk
      have hlit : Bu32lit 1 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i bl r₁ hbl
        obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨bb, hbb, hdb⟩ := decList_sound readByte_sound r₀ bl r₁ hbl
        refine ⟨bt ++ bb, by rw [hbt, hbb, hr]; simp, ?_⟩
        rw [← hv]
        exact Bdata.passive bt bb bl hlit hdb
    · rename_i hk
      have hlit : Bu32lit 2 bt := ⟨t, hdt, hk⟩
      split at h
      · cases h
      · rename_i x r₁ hx
        split at h
        · cases h
        · rename_i e r₂ he
          split at h
          · cases h
          · rename_i bl r₃ hbl
            obtain ⟨hv, hr⟩ := Prod.mk.inj (Except.ok.inj h)
            obtain ⟨bx, hbx, hdx⟩ := decIdx_sound r₀ x r₁ hx
            obtain ⟨be, hbe, hde⟩ := decExpr_sound d r₁ e r₂ he
            obtain ⟨bb, hbb, hdb⟩ := decList_sound readByte_sound r₂ bl r₃ hbl
            refine ⟨bt ++ bx ++ be ++ bb, by rw [hbt, hbx, hbe, hbb, hr]; simp, ?_⟩
            rw [← hv]
            exact Bdata.active bt bx be bb x e bl hlit hdx hde hdb
    · cases h


/-! ## Fixed byte sequences -/

/-- Consume a fixed sequence of terminal bytes. -/
def expectBytes : List Nat → Bytes → Except Fault Bytes
  | [], bs => .ok bs
  | n :: ns, bs =>
      match expectByte n bs with
      | .error e => .error e
      | .ok r => expectBytes ns r

theorem expectBytes_ok : ∀ (ns : List Nat), (∀ n ∈ ns, n < 0x100) →
    ∀ (bs r : Bytes), expectBytes ns bs = .ok r → bs = ns.map tb ++ r := by
  intro ns
  induction ns with
  | nil => intro _ bs r h; rw [expectBytes] at h; simp [Except.ok.inj h]
  | cons n ns ih =>
      intro hlt bs r h
      rw [expectBytes] at h
      split at h
      · cases h
      · rename_i r₁ hr₁
        have h1 := expectByte_ok (hlt n (by simp)) hr₁
        have h2 := ih (fun m hm => hlt m (by simp [hm])) r₁ r h
        rw [h1, h2]
        simp

/-! ## One position of the module production

Every section is preceded by a run of custom sections; `step` is that pair. -/

/-- A run of custom sections followed by one (possibly absent) section. -/
def step {α : Type} (d N : Nat) (inner : Bytes → Except Fault (List α × Bytes))
    (bs : Bytes) : Except Fault (List α × Bytes) :=
  match decCustoms d bs with
  | .error e => .error e
  | .ok b₁ => decSection N inner b₁

theorem step_sound {α : Type} {G : Bytes → List α → Prop}
    {inner : Bytes → Except Fault (List α × Bytes)} (hI : Sound G inner) (d N : Nat)
    (hN : N < 0x100) (bs : Bytes) (xs : List α) (r : Bytes)
    (h : step d N inner bs = .ok (xs, r)) :
    ∃ c us bsec, bs = c ++ bsec ++ r ∧ Star Bcustomsec c us ∧ Bsection N G bsec xs := by
  rw [step] at h
  split at h
  · cases h
  · rename_i b₁ hb₁
    obtain ⟨c, us, hc, hus⟩ := decCustoms_sound d bs b₁ hb₁
    obtain ⟨bsec, hbsec, hsec⟩ := decSection_sound hI N hN b₁ xs r h
    exact ⟨c, us, bsec, by rw [hc, hbsec]; simp, hus, hsec⟩

/-! ## The module -/

/-- `$opt_(X, x*)`: the pinned `0.3-aux.seq.spectec` function, defined on `eps`
and on a single element and nowhere else. -/
def optOf1 {α : Type} : List α → Option (Option α)
  | [] => some none
  | [x] => some (some x)
  | _ => none

theorem optOf1_sound {α : Type} : ∀ (l : List α) (o : Option α),
    optOf1 l = some o → l = o.toList := by
  intro l
  cases l with
  | nil => intro o h; rw [optOf1] at h; rw [← Option.some.inj h]; rfl
  | cons x xs =>
      cases xs with
      | nil => intro o h; rw [optOf1] at h; rw [← Option.some.inj h]; rfl
      | cons y ys => intro o h; exact absurd h (by simp [optOf1])

/-- `-- (if n = |data*|)?`. -/
def cntAgrees : Option U32 → Nat → Bool
  | none, _ => true
  | some k, len => k.val = len

/-- `-- if (n? =/= eps \/ $dataidx_funcs(func*) = eps)`. -/
def cntPresentOrNoData : Option U32 → List Func → Bool
  | some _, _ => true
  | none, funcs => (dataIdxFuncs funcs).isEmpty



/-- The side conditions of the pinned production, checked rather than assumed. -/
def finishModule (types : List TypeDef) (imports : List Import) (typeidxs : List TypeIdx)
    (tables : List Table) (mems : List Mem) (tags : List Tag) (globals : List Global)
    (exports : List Export) (starts : List Start) (elems : List Elem)
    (cnts : List U32) (codes : List Code) (datas : List Data) : Except Fault Module :=
  match optOf1 starts, optOf1 cnts with
  | some st, some n =>
      if typeidxs.length = codes.length then
        (if cntAgrees n datas.length &&
            cntPresentOrNoData n (List.zipWith
              (fun (x : TypeIdx) (c : Code) =>
                ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes) then
           .ok { types := types, imports := imports, tags := tags, globals := globals,
                 mems := mems, tables := tables,
                 funcs := List.zipWith
                   (fun (x : TypeIdx) (c : Code) =>
                     ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes,
                 datas := datas, elems := elems, start := st, exports := exports }
         else .error .side)
      else .error .side
  | _, _ => .error .section_

/-- `grammar Bmodule : module`, the whole pinned production. -/
def decModule (bs : Bytes) : Except Fault Module :=
  match expectBytes [0x00, 0x61, 0x73, 0x6D] bs with
  | .error e => .error e
  | .ok a₀ =>
      match expectBytes [0x01, 0x00, 0x00, 0x00] a₀ with
      | .error e => .error e
      | .ok a₁ =>
          match step bs.length 1 (decList decType) a₁ with
          | .error e => .error e
          | .ok (types, a₂) =>
              match step bs.length 2 (decList decImport) a₂ with
              | .error e => .error e
              | .ok (imports, a₃) =>
                  match step bs.length 3 (decList decIdx) a₃ with
                  | .error e => .error e
                  | .ok (typeidxs, a₄) =>
                      match step bs.length 4 (decList (decTable bs.length)) a₄ with
                      | .error e => .error e
                      | .ok (tables, a₅) =>
                          match step bs.length 5 (decList decMem) a₅ with
                          | .error e => .error e
                          | .ok (mems, a₆) =>
                              match step bs.length 13 (decList decTag) a₆ with
                              | .error e => .error e
                              | .ok (tags, a₇) =>
                                  match step bs.length 6 (decList (decGlobal bs.length)) a₇ with
                                  | .error e => .error e
                                  | .ok (globals, a₈) =>
                                      match step bs.length 7 (decList decExport) a₈ with
                                      | .error e => .error e
                                      | .ok (exports, a₉) =>
                                          match step bs.length 8 decStart a₉ with
                                          | .error e => .error e
                                          | .ok (starts, a₁₀) =>
                                              match step bs.length 9 (decList (decElem bs.length)) a₁₀ with
                                              | .error e => .error e
                                              | .ok (elems, a₁₁) =>
                                                  match step bs.length 12 decDatacnt a₁₁ with
                                                  | .error e => .error e
                                                  | .ok (cnts, a₁₂) =>
                                                      match step bs.length 10 (decList (decCode bs.length)) a₁₂ with
                                                      | .error e => .error e
                                                      | .ok (codes, a₁₃) =>
                                                          match step bs.length 11 (decList (decData bs.length)) a₁₃ with
                                                          | .error e => .error e
                                                          | .ok (datas, a₁₄) =>
                                                              match decCustoms bs.length a₁₄ with
                                                              | .error e => .error e
                                                              | .ok a₁₅ =>
                                                                  if a₁₅.isEmpty then
                                                                    finishModule types imports
                                                                      typeidxs tables mems tags
                                                                      globals exports starts elems
                                                                      cnts codes datas
                                                                  else .error .trailing

/-! ## Soundness of the module decoder -/

theorem finishModule_sound {types : List TypeDef} {imports : List Import}
    {typeidxs : List TypeIdx} {tables : List Table} {mems : List Mem}
    {tags : List Tag} {globals : List Global} {exports : List Export}
    {starts : List Start} {elems : List Elem} {cnts : List U32}
    {codes : List Code} {datas : List Data} {m : Module}
    (h : finishModule types imports typeidxs tables mems tags globals exports
      starts elems cnts codes datas = .ok m) :
    ∃ (st : Option Start) (n : Option U32) (funcs : List Func),
      starts = st.toList ∧ cnts = n.toList ∧
      typeidxs.length = codes.length ∧
      funcs = List.zipWith (fun (x : TypeIdx) (c : Code) =>
        ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes ∧
      (∀ k : U32, n = some k → k.val = datas.length) ∧
      (n ≠ none ∨ dataIdxFuncs funcs = []) ∧
      m = { types := types, imports := imports, tags := tags, globals := globals,
            mems := mems, tables := tables,
            funcs := List.zipWith (fun (x : TypeIdx) (c : Code) =>
              ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes,
            datas := datas, elems := elems, start := st, exports := exports } := by
  rw [finishModule] at h
  split at h
  · rename_i st n hst hcnt
    split at h
    · rename_i hlen
      split at h
      · rename_i hside
        obtain ⟨hs1, hs2⟩ := Bool.and_eq_true _ _ |>.mp hside
        refine ⟨st, n, _, optOf1_sound starts st hst, optOf1_sound cnts n hcnt,
          hlen, rfl, ?_, ?_, (Except.ok.inj h).symm⟩
        · intro k hk
          rw [hk] at hs1
          rw [cntAgrees] at hs1
          exact of_decide_eq_true hs1
        · cases n with
          | none =>
              right
              rw [cntPresentOrNoData] at hs2
              exact List.isEmpty_iff.mp hs2
          | some k => left; simp
      · cases h
    · cases h
  · cases h

theorem decModule_sound (bs : Bytes) (m : Module) (h : decModule bs = .ok m) :
    Bmodule bs m := by
  rw [decModule] at h
  split at h
  · cases h
  · rename_i a₀ e₀
    split at h
    · cases h
    · rename_i a₁ e₁
      split at h
      · cases h
      · rename_i types a₂ e₂
        split at h
        · cases h
        · rename_i imports a₃ e₃
          split at h
          · cases h
          · rename_i typeidxs a₄ e₄
            split at h
            · cases h
            · rename_i tables a₅ e₅
              split at h
              · cases h
              · rename_i mems a₆ e₆
                split at h
                · cases h
                · rename_i tags a₇ e₇
                  split at h
                  · cases h
                  · rename_i globals a₈ e₈
                    split at h
                    · cases h
                    · rename_i exports a₉ e₉
                      split at h
                      · cases h
                      · rename_i starts a₁₀ e₁₀
                        split at h
                        · cases h
                        · rename_i elems a₁₁ e₁₁
                          split at h
                          · cases h
                          · rename_i cnts a₁₂ e₁₂
                            split at h
                            · cases h
                            · rename_i codes a₁₃ e₁₃
                              split at h
                              · cases h
                              · rename_i datas a₁₄ e₁₄
                                split at h
                                · cases h
                                · rename_i a₁₅ e₁₅
                                  split at h
                                  · rename_i hempty
                                    have ha₁₅ : a₁₅ = [] := by
                                      cases a₁₅ with
                                      | nil => rfl
                                      | cons _ _ => simp at hempty
                                    have hmag := expectBytes_ok [0x00, 0x61, 0x73, 0x6D] (by decide) bs a₀ e₀
                                    have hver := expectBytes_ok [0x01, 0x00, 0x00, 0x00] (by decide) a₀ a₁ e₁
                                    obtain ⟨c₀, u₀, bty, hq₀, hu₀, hdbty⟩ :=
                                      step_sound (decList_sound decType_sound) bs.length 1 (by decide) a₁ types a₂ e₂
                                    obtain ⟨c₁, u₁, bim, hq₁, hu₁, hdbim⟩ :=
                                      step_sound (decList_sound decImport_sound) bs.length 2 (by decide) a₂ imports a₃ e₃
                                    obtain ⟨c₂, u₂, bfu, hq₂, hu₂, hdbfu⟩ :=
                                      step_sound (decList_sound decIdx_sound) bs.length 3 (by decide) a₃ typeidxs a₄ e₄
                                    obtain ⟨c₃, u₃, bta, hq₃, hu₃, hdbta⟩ :=
                                      step_sound (decList_sound (decTable_sound bs.length)) bs.length 4 (by decide) a₄ tables a₅ e₅
                                    obtain ⟨c₄, u₄, bme, hq₄, hu₄, hdbme⟩ :=
                                      step_sound (decList_sound decMem_sound) bs.length 5 (by decide) a₅ mems a₆ e₆
                                    obtain ⟨c₅, u₅, btg, hq₅, hu₅, hdbtg⟩ :=
                                      step_sound (decList_sound decTag_sound) bs.length 13 (by decide) a₆ tags a₇ e₇
                                    obtain ⟨c₆, u₆, bgl, hq₆, hu₆, hdbgl⟩ :=
                                      step_sound (decList_sound (decGlobal_sound bs.length)) bs.length 6 (by decide) a₇ globals a₈ e₈
                                    obtain ⟨c₇, u₇, bex, hq₇, hu₇, hdbex⟩ :=
                                      step_sound (decList_sound decExport_sound) bs.length 7 (by decide) a₈ exports a₉ e₉
                                    obtain ⟨c₈, u₈, bst, hq₈, hu₈, hdbst⟩ :=
                                      step_sound decStart_sound bs.length 8 (by decide) a₉ starts a₁₀ e₁₀
                                    obtain ⟨c₉, u₉, bel, hq₉, hu₉, hdbel⟩ :=
                                      step_sound (decList_sound (decElem_sound bs.length)) bs.length 9 (by decide) a₁₀ elems a₁₁ e₁₁
                                    obtain ⟨c₁₀, u₁₀, bdc, hq₁₀, hu₁₀, hdbdc⟩ :=
                                      step_sound decDatacnt_sound bs.length 12 (by decide) a₁₁ cnts a₁₂ e₁₂
                                    obtain ⟨c₁₁, u₁₁, bco, hq₁₁, hu₁₁, hdbco⟩ :=
                                      step_sound (decList_sound (decCode_sound bs.length)) bs.length 10 (by decide) a₁₂ codes a₁₃ e₁₃
                                    obtain ⟨c₁₂, u₁₂, bda, hq₁₂, hu₁₂, hdbda⟩ :=
                                      step_sound (decList_sound (decData_sound bs.length)) bs.length 11 (by decide) a₁₃ datas a₁₄ e₁₄
                                    obtain ⟨c₁₃, u₁₃, hq₁₃, hu₁₃⟩ := decCustoms_sound bs.length a₁₄ a₁₅ e₁₅
                                    obtain ⟨st, n, funcs, hst, hn, hlen, hfuncs, hs1, hs2, hm⟩ := finishModule_sound h
                                    have hstart : Bstartsec bst st := by
                                      cases st with
                                      | none =>
                                          have h0 : starts = [] := hst
                                          rw [h0] at hdbst
                                          exact Bstartsec.absent bst hdbst
                                      | some sv =>
                                          have h0 : starts = [sv] := hst
                                          rw [h0] at hdbst
                                          exact Bstartsec.present bst sv hdbst
                                    have hdcnt : Bdatacntsec bdc n := by
                                      cases n with
                                      | none =>
                                          have h0 : cnts = [] := hn
                                          rw [h0] at hdbdc
                                          exact Bdatacntsec.absent bdc hdbdc
                                      | some kv =>
                                          have h0 : cnts = [kv] := hn
                                          rw [h0] at hdbdc
                                          exact Bdatacntsec.present bdc kv hdbdc
                                    have hbs : bs = [tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ [tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfu ++ c₃ ++ bta ++ c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++ c₉ ++ bel ++ c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃ := by
                                      rw [hmag, hver, hq₀, hq₁, hq₂, hq₃, hq₄, hq₅, hq₆, hq₇, hq₈, hq₉, hq₁₀, hq₁₁, hq₁₂, hq₁₃, ha₁₅]
                                      simp
                                    rw [hfuncs] at hs2
                                    rw [hbs, hm]
                                    exact Bmodule.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bmagic.mk Bversion.mk hu₀ hdbty hu₁ hdbim hu₂ hdbfu hu₃ hdbta hu₄ hdbme hu₅ hdbtg hu₆ hdbgl hu₇ hdbex hu₈ hstart hu₉ hdbel hu₁₀ hdcnt hu₁₁ hdbco hu₁₂ hdbda hu₁₃ hs1 hs2 hlen rfl
                                  · cases h


end WasmGemmGnaf.Wasm.Core.Decode
