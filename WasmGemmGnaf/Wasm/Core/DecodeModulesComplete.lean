/-
  Wasm/Core/DecodeModulesComplete.lean --- COMPLETENESS of the executable
  Core 3.0 module decoder against `Wasm/Core/BinaryGrammar/Modules.lean`.

  WHAT IS PROVED HERE.

      decModule_complete : Bmodule bs m -> decModule bs = .ok m

  -- every derivation of the pinned `Bmodule` is decoded, to the module the
  derivation produces.  Together with `decModule_sound` this says the executable
  decoder and the transcribed grammar accept exactly the same byte sequences and
  agree on the value.

  WHY COMPLETENESS IS THE DIRECTION THAT MATTERS FOR THE RELEASE CLAIM.
  Soundness alone is satisfied by a decoder that rejects everything.  A decoder
  that silently rejected a valid module would SHRINK the set of programs the
  optimality statement quantifies over, which is exactly the narrowing four
  external audits objected to.

  THE FOUR PLACES A GREEDY DECODER COULD DISAGREE WITH THE GRAMMAR, AND HOW EACH
  IS DISCHARGED.

  * NON-MINIMAL LEB128.  `Bu32` derives `0x80 0x00` for `0`; the decoder accepts
    it, and `decU32_complete` is what says so.  Nothing below assumes a canonical
    encoding anywhere, including for the `k:Bu32` selector of a prefixed opcode
    and for the `0:Bu32` tag of an element or data segment.

  * CUSTOM SECTIONS.  `Bcustomsec` may derive `eps` (its `Bsection` has an
    `absent` alternative), so a `Star Bcustomsec` run may be split anywhere, and
    the decoder consumes a MAXIMAL run instead.  `decCustoms_absorb` and
    `decCustoms_run` reconcile the two: absorbing a derivable custom run in front
    of a byte sequence does not change what the decoder does with the rest.

  * ABSENT SECTIONS.  The pinned section ORDER is `1 2 3 4 5 13 6 7 8 9 12 10 11`
    -- not the numeric order -- and any section may be absent.  When one is, the
    decoder's `decCustoms` at that position eats the custom runs of the following
    absent positions too.  `secTail_decCustoms` is a byte-level lemma over the
    remaining segment list that computes exactly where the run stops, so the
    thirteen positions compose without a case split on which sections are
    present.

  * THE SIDE CONDITIONS.  `finishModule_complete` shows the three starred
    conditions of the pinned production -- the data count agreement, the
    data-count-present-or-no-data-index condition, and the function/code pairing
    -- are ACCEPTED by the checker exactly when the grammar's hypotheses hold.

  CHOICE-FREE.  `decode_complete` is an executable witness under SPEC 4, so its
  axiom closure must be `[propext, Quot.sound]`.  Every `omega` below whose goal
  is not already `False` is preceded by `exfalso`, and no conjunctive goal is
  handed to `omega`, because either would put `Classical.choice` in the closure.
-/
import WasmGemmGnaf.Wasm.Core.DecodeModules
import WasmGemmGnaf.Wasm.Core.DecodeInstrComplete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace WasmGemmGnaf.Wasm.Core.Decode

open WasmGemmGnaf.Wasm.Core
open WasmGemmGnaf.Wasm.Core.Binary

/-! ## Completeness at a fuel

The decoders of the module layer that reach an expression carry the fuel `d` of
`decExpr`; `CompleteD` is `Complete` for such a family, with the derivation's own
length as the fuel bound. -/

/-- `p` derives everything `G` derives, at every fuel at least the length of the
derivation. -/
def CompleteD {α : Type} (G : Bytes → α → Prop) (p : Nat → Step α) : Prop :=
  ∀ (d : Nat) (b : Bytes) (x : α) (r : Bytes), b.length ≤ d → G b x →
    p d (b ++ r) = .ok (x, r)

/-- A fuel-free complete parser is complete at every fuel. -/
theorem CompleteD.of_complete {α : Type} {G : Bytes → α → Prop} {p : Step α}
    (h : Complete G p) : CompleteD G (fun _ => p) :=
  fun _ b x r _ hx => h b x r hx

theorem decRep_completeD {α : Type} {G : Bytes → α → Prop} {p : Nat → Step α}
    (hp : CompleteD G p) (d n : Nat) :
    ∀ (b : Bytes) (xs : List α), Rep G n b xs → ∀ (r : Bytes), b.length ≤ d →
      decRep (p d) n (b ++ r) = .ok (xs, r) := by
  intro b xs h
  induction h with
  | nil => intro r _; rfl
  | cons b₁ x b₂ ys k hd₁ _ ih =>
      intro r hd
      have hl1 : b₁.length ≤ d := by simp only [List.length_append] at hd; omega
      have hl2 : b₂.length ≤ d := by simp only [List.length_append] at hd; omega
      rw [List.append_assoc]
      simp only [decRep, hp d b₁ x (b₂ ++ r) hl1 hd₁, ih r hl2]

theorem decList_completeD {α : Type} {G : Bytes → α → Prop} {p : Nat → Step α}
    (hp : CompleteD G p) : CompleteD (Blist G) (fun d => decList (p d)) := by
  intro d b xs r hd h
  cases h with
  | mk bn bs n _ys hn hrep =>
      have hl : bs.length ≤ d := by
        simp only [List.length_append] at hd; omega
      rw [List.append_assoc]
      simp only [decList, decU32_complete bn n (bs ++ r) hn]
      exact decRep_completeD hp d n.val bs xs hrep r hl

/-! ## Custom sections

`decCustoms` consumes a MAXIMAL run of custom sections.  The grammar's
`Star Bcustomsec` need not be maximal, and may even contain absent
(`eps`-deriving) custom sections; these four lemmas reconcile the two. -/

/-- `(x ++ y).take x.length = x`, in the shape the section decoder needs. -/
theorem takeLeft (x y : Bytes) : (x ++ y).take x.length = x := by simp

/-- `(x ++ y).drop x.length = y`, in the shape the section decoder needs. -/
theorem dropLeft (x y : Bytes) : (x ++ y).drop x.length = y := by simp

/-- A byte sequence that cannot begin a custom section. -/
def notCust : Bytes → Prop
  | [] => True
  | b :: _ => ¬ (b.val = 0x00)

theorem decCustoms_id : ∀ (n : Nat) (r : Bytes), notCust r → decCustoms n r = .ok r := by
  intro n
  cases n with
  | zero => intro r _; rfl
  | succ n =>
      intro r hr
      cases r with
      | nil => rfl
      | cons b t => rw [decCustoms]; exact if_neg hr

/-- The fuel does not matter once it is at least the length of the input. -/
theorem decCustoms_stable : ∀ (n m : Nat) (bs : Bytes), bs.length ≤ n → bs.length ≤ m →
    decCustoms n bs = decCustoms m bs := by
  intro n
  induction n with
  | zero =>
      intro m bs hn _
      have hb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hb
      cases m with
      | zero => rfl
      | succ m => rfl
  | succ n ih =>
      intro m bs hn hm
      cases bs with
      | nil => cases m with | zero => rfl | succ m => rfl
      | cons b t =>
          cases m with
          | zero => exfalso; simp only [List.length_cons] at hm; omega
          | succ m =>
              rw [decCustoms, decCustoms]
              by_cases hb : b.val = 0x00
              · simp only [if_pos hb]
                cases hu : decU32 t with
                | error e => rfl
                | ok q =>
                    obtain ⟨len, r₁⟩ := q
                    have hr₁ : r₁.length ≤ t.length := by
                      obtain ⟨bl, hbl, _⟩ := decU32_sound t len r₁ hu
                      have hc := congrArg List.length hbl
                      simp only [List.length_append] at hc
                      omega
                    simp only [hu]
                    by_cases hlen : (r₁.take len.val).length = len.val
                    · simp only [if_pos hlen]
                      cases hn' : decName (r₁.take len.val) with
                      | error e => rfl
                      | ok q2 =>
                          obtain ⟨nm, rest⟩ := q2
                          simp only [hn']
                          have hdl : (r₁.drop len.val).length = r₁.length - len.val := by simp
                          refine ih m (r₁.drop len.val) ?_ ?_
                          · simp only [List.length_cons] at hn; omega
                          · simp only [List.length_cons] at hm; omega
                    · simp only [if_neg hlen]
              · simp only [if_neg hb]

/-- A derivable run of custom sections, followed by anything that cannot begin
one, is consumed exactly. -/
theorem decCustoms_run : ∀ (k : Nat) (c : Bytes) (us : List Unit), Rep Bcustomsec k c us →
    ∀ (r : Bytes) (n : Nat), c.length ≤ n → notCust r → decCustoms n (c ++ r) = .ok r := by
  intro k c us h
  induction h with
  | nil => intro r n _ hr; exact decCustoms_id n r hr
  | cons b u bs us' k' hcust _ ih =>
      intro r n hn hr
      cases hcust with
      | mk =>
          rename_i vs hsec
          cases hsec with
          | absent =>
              refine ih r n ?_ hr
              simp only [List.nil_append, List.length_append, List.length_nil] at hn ⊢
              omega
          | present =>
              rename_i blen payload len hlen hplen hG
              cases hG with
              | mk bn bb nm bl hname _ =>
                  cases n with
                  | zero =>
                      exfalso
                      simp only [List.length_append, List.length_cons] at hn; omega
                  | succ n =>
                      have hnlen : bs.length ≤ n := by
                        simp only [List.length_append, List.length_cons] at hn; omega
                      have hrec := ih r n hnlen hr
                      have hshape : ((tb 0x00 :: (blen ++ (bn ++ bb))) ++ bs) ++ r
                          = tb 0x00 :: (blen ++ ((bn ++ bb) ++ (bs ++ r))) := by simp
                      have htake : ((bn ++ bb) ++ (bs ++ r)).take len.val = bn ++ bb := by
                        rw [hplen]; exact takeLeft (bn ++ bb) (bs ++ r)
                      have hdrop : ((bn ++ bb) ++ (bs ++ r)).drop len.val = bs ++ r := by
                        rw [hplen]; exact dropLeft (bn ++ bb) (bs ++ r)
                      rw [hshape, decCustoms]
                      simp only [if_true, tb_val 0x00 (by decide), if_pos rfl,
                        decU32_complete blen len ((bn ++ bb) ++ (bs ++ r)) hlen,
                        htake, hdrop, ← hplen, if_pos rfl,
                        decName_complete bn nm bb hname]
                      exact hrec

/-- Absorbing a derivable custom run in front of a byte sequence does not change
what the decoder makes of the rest. -/
theorem decCustoms_absorb : ∀ (k : Nat) (c : Bytes) (us : List Unit),
    Rep Bcustomsec k c us → ∀ (U : Bytes) (n : Nat), (c ++ U).length ≤ n →
      decCustoms n (c ++ U) = decCustoms n U := by
  intro k c us h
  induction h with
  | nil => intro U n _; rfl
  | cons b u bs us' k' hcust _ ih =>
      intro U n hn
      cases hcust with
      | mk =>
          rename_i vs hsec
          cases hsec with
          | absent =>
              refine ih U n ?_
              simp only [List.nil_append, List.length_append, List.length_nil] at hn ⊢
              omega
          | present =>
              rename_i blen payload len hlen hplen hG
              cases hG with
              | mk bn bb nm bl hname _ =>
                  cases n with
                  | zero =>
                      exfalso
                      simp only [List.length_append, List.length_cons] at hn; omega
                  | succ n =>
                      have hbound : (bs ++ U).length ≤ n := by
                        simp only [List.length_append, List.length_cons] at hn ⊢; omega
                      have hUbound : U.length ≤ n := by
                        simp only [List.length_append, List.length_cons] at hn ⊢; omega
                      have hrec : decCustoms n (bs ++ U) = decCustoms n U := ih U n hbound
                      have hnU : decCustoms n U = decCustoms (n + 1) U :=
                        decCustoms_stable n (n + 1) U hUbound (by omega)
                      have hshape : ((tb 0x00 :: (blen ++ (bn ++ bb))) ++ bs) ++ U
                          = tb 0x00 :: (blen ++ ((bn ++ bb) ++ (bs ++ U))) := by simp
                      have htake : ((bn ++ bb) ++ (bs ++ U)).take len.val = bn ++ bb := by
                        rw [hplen]; exact takeLeft (bn ++ bb) (bs ++ U)
                      have hdrop : ((bn ++ bb) ++ (bs ++ U)).drop len.val = bs ++ U := by
                        rw [hplen]; exact dropLeft (bn ++ bb) (bs ++ U)
                      rw [hshape, decCustoms]
                      simp only [if_true, tb_val 0x00 (by decide), if_pos rfl,
                        decU32_complete blen len ((bn ++ bb) ++ (bs ++ U)) hlen,
                        htake, hdrop, ← hplen, if_pos rfl,
                        decName_complete bn nm bb hname]
                      rw [hrec, hnU]

/-! ## Sections -/

/-- A byte sequence that does not begin section `N`. -/
def notSec (N : Nat) : Bytes → Prop
  | [] => True
  | b :: _ => ¬ (b.val = N)

theorem decSection_completeD {α : Type} {G : Bytes → List α → Prop}
    {inner : Nat → Bytes → Except Fault (List α × Bytes)}
    (hI : CompleteD G inner) (N : Nat) (hN : N < 0x100) (d : Nat)
    (bsec : Bytes) (xs : List α) (h : Bsection N G bsec xs) (r : Bytes)
    (hd : bsec.length ≤ d) (hr : bsec = [] → notSec N r) :
    decSection N (inner d) (bsec ++ r) = .ok (xs, r) := by
  cases h with
  | absent =>
      show decSection N (inner d) r = _
      have hr' := hr rfl
      cases r with
      | nil => rfl
      | cons b t =>
          rw [decSection]
          exact if_neg hr'
  | present =>
      rename_i blen bpay len hlen hplen hG
      have hbd : bpay.length ≤ d := by
        simp only [List.length_cons, List.length_append] at hd; omega
      have htake : (bpay ++ r).take len.val = bpay := by
        rw [hplen]; exact takeLeft bpay r
      have hdrop : (bpay ++ r).drop len.val = r := by
        rw [hplen]; exact dropLeft bpay r
      have hinner : inner d bpay = .ok (xs, []) := by
        have := hI d bpay xs [] hbd hG
        simpa using this
      have hshape : (tb N :: (blen ++ bpay)) ++ r = tb N :: (blen ++ (bpay ++ r)) := by simp
      rw [hshape, decSection]
      simp only [tb_val N hN, if_pos rfl,
        decU32_complete blen len (bpay ++ r) hlen, htake, hdrop, ← hplen, if_pos rfl,
        hinner, List.isEmpty_nil, if_true]

/-! ## The thirteen positions of the pinned module production

The section order of `Bmodule` is `1 2 3 4 5 13 6 7 8 9 12 10 11`, every section
may be absent, and a run of custom sections sits before each one and after the
last.  A decoder that eats a MAXIMAL custom run at each position therefore does
not split the byte sequence the way the derivation does.  `Seg` and the four
lemmas below are the byte-level reconciliation, uniform in the position, so the
module proof composes thirteen identical steps. -/

/-- One position: the section id, the custom run before it, and its own bytes
(empty exactly when the section is absent). -/
structure Seg where
  /-- the section id. -/
  id : Nat
  /-- the custom-section run before this section. -/
  pre : Bytes
  /-- the section's own bytes; `[]` when the section is absent. -/
  body : Bytes

/-- A byte sequence derivable as `Bcustomsec*`. -/
def CustRun (c : Bytes) : Prop := ∃ (k : Nat) (us : List Unit), Rep Bcustomsec k c us

/-- What the module production guarantees about one position. -/
structure SegOk (s : Seg) : Prop where
  /-- the run before it really is a run of custom sections. -/
  pre_cust : CustRun s.pre
  /-- section ids are bytes. -/
  id_lt : s.id < 0x100
  /-- no section has id `0`; that is the custom section's id. -/
  id_ne : s.id ≠ 0
  /-- a present section begins with its id byte. -/
  body_shape : s.body = [] ∨ ∃ t, s.body = tb s.id :: t

/-- The byte sequence of a list of positions, followed by the trailing run. -/
def segsBytes : List Seg → Bytes → Bytes
  | [], post => post
  | s :: rest, post => s.pre ++ (s.body ++ segsBytes rest post)

/-- What the decoder's maximal custom run leaves: everything from the first
PRESENT section on. -/
def strip : List Seg → Bytes → Bytes
  | [], _ => []
  | s :: rest, post =>
      if s.body = [] then strip rest post else s.body ++ segsBytes rest post

theorem strip_shape : ∀ (segs : List Seg) (post : Bytes), (∀ s ∈ segs, SegOk s) →
    strip segs post = [] ∨ ∃ s, s ∈ segs ∧ ∃ t, strip segs post = tb s.id :: t := by
  intro segs
  induction segs with
  | nil => intro post _; exact Or.inl rfl
  | cons s rest ih =>
      intro post hok
      by_cases hb : s.body = []
      · have hrec := ih post (fun t ht => hok t (by simp [ht]))
        rw [strip, if_pos hb]
        rcases hrec with h | ⟨t, ht, u, hu⟩
        · exact Or.inl h
        · exact Or.inr ⟨t, by simp [ht], u, hu⟩
      · rcases (hok s (by simp)).body_shape with h | ⟨u, hu⟩
        · exact absurd h hb
        · refine Or.inr ⟨s, by simp, u ++ segsBytes rest post, ?_⟩
          rw [strip, if_neg hb, hu]
          simp

theorem strip_notCust (segs : List Seg) (post : Bytes) (hok : ∀ s ∈ segs, SegOk s) :
    notCust (strip segs post) := by
  rcases strip_shape segs post hok with h | ⟨s, hs, t, ht⟩
  · rw [h]; trivial
  · rw [ht]
    show ¬ ((tb s.id).val = 0x00)
    rw [tb_val s.id (hok s hs).id_lt]
    exact (hok s hs).id_ne

theorem strip_notSec (segs : List Seg) (post : Bytes) (N : Nat) (hN : N < 0x100)
    (hok : ∀ s ∈ segs, SegOk s) (hne : ∀ s ∈ segs, s.id ≠ N) :
    notSec N (strip segs post) := by
  rcases strip_shape segs post hok with h | ⟨s, hs, t, ht⟩
  · rw [h]; trivial
  · rw [ht]
    show ¬ ((tb s.id).val = N)
    rw [tb_val s.id (hok s hs).id_lt]
    exact hne s hs

theorem strip_length_le : ∀ (segs : List Seg) (post : Bytes),
    (strip segs post).length ≤ (segsBytes segs post).length := by
  intro segs
  induction segs with
  | nil => intro post; simp [strip, segsBytes]
  | cons s rest ih =>
      intro post
      by_cases hb : s.body = []
      · rw [strip, if_pos hb, segsBytes, hb]
        have := ih post
        simp only [List.length_append, List.length_nil]
        omega
      · rw [strip, if_neg hb, segsBytes]
        simp only [List.length_append]
        omega

/-- The decoder's maximal custom run, computed. -/
theorem decCustoms_segs : ∀ (segs : List Seg) (post : Bytes), (∀ s ∈ segs, SegOk s) →
    CustRun post → ∀ (n : Nat), (segsBytes segs post).length ≤ n →
      decCustoms n (segsBytes segs post) = .ok (strip segs post) := by
  intro segs
  induction segs with
  | nil =>
      intro post _ hpost n hn
      obtain ⟨k, us, hrep⟩ := hpost
      have := decCustoms_run k post us hrep [] n (by simpa [segsBytes] using hn) trivial
      simpa [segsBytes] using this
  | cons s rest ih =>
      intro post hok hpost n hn
      obtain ⟨k, us, hrep⟩ := (hok s (by simp)).pre_cust
      have hlen : (s.pre ++ (s.body ++ segsBytes rest post)).length ≤ n := by
        simpa [segsBytes] using hn
      have habs := decCustoms_absorb k s.pre us hrep (s.body ++ segsBytes rest post) n hlen
      rw [segsBytes, habs]
      by_cases hb : s.body = []
      · rw [strip, if_pos hb, hb, List.nil_append]
        refine ih post (fun t ht => hok t (by simp [ht])) hpost n ?_
        simp only [List.length_append, List.length_nil, hb] at hlen ⊢
        omega
      · rcases (hok s (by simp)).body_shape with h | ⟨u, hu⟩
        · exact absurd h hb
        · rw [strip, if_neg hb]
          refine decCustoms_id n _ ?_
          rw [hu]
          show ¬ ((tb s.id).val = 0x00)
          rw [tb_val s.id (hok s (by simp)).id_lt]
          exact (hok s (by simp)).id_ne

/-- ONE POSITION OF THE MODULE PRODUCTION.  The decoder consumes the custom run
and the section, and what is left is again in the shape the next position needs.
Uniform in whether the section is present. -/
theorem step_complete {α : Type} {G : Bytes → List α → Prop}
    {inner : Nat → Bytes → Except Fault (List α × Bytes)} (hI : CompleteD G inner)
    (d n N : Nat) (pre body : Bytes) (rest : List Seg) (post : Bytes)
    (xs : List α) (X : Bytes)
    (hok : ∀ t ∈ ((⟨N, pre, body⟩ : Seg) :: rest), SegOk t) (hpost : CustRun post)
    (hne : ∀ t ∈ rest, t.id ≠ N)
    (hsec : Bsection N G body xs) (hbd : body.length ≤ d)
    (hn : (segsBytes ((⟨N, pre, body⟩ : Seg) :: rest) post).length ≤ n)
    (hX : decCustoms n X = .ok (strip ((⟨N, pre, body⟩ : Seg) :: rest) post)) :
    ∃ Y, step n N (inner d) X = .ok (xs, Y) ∧
      decCustoms n Y = .ok (strip rest post) := by
  have hokr : ∀ t ∈ rest, SegOk t := fun t ht => hok t (by simp [ht])
  have hN : N < 0x100 := (hok ⟨N, pre, body⟩ (by simp)).id_lt
  have hnr : (segsBytes rest post).length ≤ n := by
    simp only [segsBytes, List.length_append] at hn
    omega
  cases hsec with
  | absent =>
      refine ⟨strip rest post, ?_, ?_⟩
      · rw [step, hX]
        have hs : strip ((⟨N, pre, []⟩ : Seg) :: rest) post = strip rest post := by
          rw [strip]; exact if_pos rfl
        rw [hs]
        have := decSection_completeD hI N hN d [] [] Bsection.absent (strip rest post)
          (by simp) (fun _ => strip_notSec rest post N hN hokr hne)
        simpa using this
      · exact decCustoms_id n _ (strip_notCust rest post hokr)
  | present =>
      rename_i blen bpay len hlen hplen hG
      refine ⟨segsBytes rest post, ?_, ?_⟩
      · rw [step, hX]
        have hbne : ¬ ((tb N :: (blen ++ bpay)) = []) := by simp
        have hs : strip ((⟨N, pre, tb N :: (blen ++ bpay)⟩ : Seg) :: rest) post
            = (tb N :: (blen ++ bpay)) ++ segsBytes rest post := by
          rw [strip]; exact if_neg hbne
        rw [hs]
        exact decSection_completeD hI N hN d (tb N :: (blen ++ bpay)) xs
          (Bsection.present blen bpay len xs hlen hG hplen) (segsBytes rest post) hbd
          (fun hcon => absurd hcon hbne)
      · exact decCustoms_segs rest post hokr hpost n hnr

/-! ## The section payloads

One completeness theorem per `grammar B<section-item>` of
`5.4-binary.modules.spectec`. -/

/-- `Bexpr` as a `CompleteD`. -/
theorem decExpr_CompleteD [authority : BinaryAuthority] : CompleteD Bexpr decExpr :=
  fun d b e r hd h => decExpr_completeD d b e r hd h

theorem decType_complete [authority : BinaryAuthority] : Complete Btype decType := by
  intro b t r h
  cases h with
  | mk => rename_i qt hq; simp only [decType, decRectype_complete _ qt r hq]

theorem decImport_complete [authority : BinaryAuthority] : Complete Bimport decImport := by
  intro b im r h
  cases h with
  | mk b₁ b₂ b₃ nm₁ nm₂ xt h₁ h₂ h₃ =>
      rw [show b₁ ++ b₂ ++ b₃ ++ r = b₁ ++ (b₂ ++ (b₃ ++ r)) from by simp]
      simp only [decImport, decName_complete b₁ nm₁ (b₂ ++ (b₃ ++ r)) h₁,
        decName_complete b₂ nm₂ (b₃ ++ r) h₂, decExterntype_complete b₃ xt r h₃]

theorem decMem_complete : Complete Bmem decMem := by
  intro b m r h
  cases h with
  | mk => rename_i mt hm; simp only [decMem, decMemtype_complete _ mt r hm]

theorem decTag_complete : Complete Btag decTag := by
  intro b t r h
  cases h with
  | mk => rename_i jt hj; simp only [decTag, decTagtype_complete _ jt r hj]

theorem decExport_complete : Complete Bexport decExport := by
  intro b ex r h
  cases h with
  | mk bn bx nm xx hn hx =>
      rw [show bn ++ bx ++ r = bn ++ (bx ++ r) from by simp]
      simp only [decExport, decName_complete bn nm (bx ++ r) hn,
        decExternidx_complete bx xx r hx]

theorem decStart_complete : Complete Bstart decStart := by
  intro b ss r h
  cases h with
  | mk => rename_i x hx; simp only [decStart, decIdx_complete _ x r hx]

theorem decDatacnt_complete : Complete Bdatacnt decDatacnt := by
  intro b ns r h
  cases h with
  | mk => rename_i n hn; simp only [decDatacnt, decU32_complete _ n r hn]

theorem decElemkind_complete : Complete Belemkind decElemkind := by
  intro b rt r h
  cases h with
  | funcref =>
      show decElemkind (tb 0x00 :: r) = _
      simp only [decElemkind, expectByte_eq 0x00 (by decide) r]

theorem decLocals_complete [authority : BinaryAuthority] : Complete Blocals decLocals := by
  intro b ls r h
  cases h with
  | mk bn bt n t hn ht =>
      rw [show bn ++ bt ++ r = bn ++ (bt ++ r) from by simp]
      simp only [decLocals, decU32_complete bn n (bt ++ r) hn,
        decValtype_complete bt t r ht]

/-- Every `Breftype` derivation begins with a byte other than `0x40`, which is
what separates the shorthand table form from the `0x40 0x00` form. -/
theorem Breftype_head [authority : BinaryAuthority]
    {bs : Bytes} {rt : RefType} (h : Breftype bs rt) :
    ∃ b u, bs = b :: u ∧ ¬ (b.val = 0x40) := by
  obtain ⟨b, u, hb, hne, _⟩ := Bvaltype_head (Bvaltype.ref bs rt h)
  exact ⟨b, u, hb, hne⟩

/-- Every `Btabletype` derivation begins with a byte other than `0x40`, so the
shorthand table form and the `0x40 0x00` form are separated by the first byte. -/
theorem Btabletype_head [authority : BinaryAuthority]
    {bs : Bytes} {tt : TableType} (h : Btabletype bs tt) :
    ∃ c u, bs = c :: u ∧ ¬ (c.val = 0x40) := by
  cases h with
  | mk br bl rt at' lim hr hl =>
      obtain ⟨c, u, hc, hcne⟩ := Breftype_head hr
      exact ⟨c, u ++ bl, by rw [hc]; simp, hcne⟩

theorem decTable_completeD [authority : BinaryAuthority] : CompleteD Btable decTable := by
  intro d b tab r hd h
  cases h with
  | shorthand =>
      rename_i tt nul ht helem htt
      obtain ⟨c, u, hc, hcne⟩ := Btabletype_head htt
      have hstep : decTabletype (b ++ r) = .ok (tt, r) := decTabletype_complete b tt r htt
      rw [hc] at hstep ⊢
      simp only [List.cons_append] at hstep
      show decTable d (c :: (u ++ r)) = _
      rw [decTable, if_neg hcne]
      simp only [hstep]
      rw [helem]
  | withInit bt be tt e htt he =>
      have hlt : bt.length ≤ d ∧ be.length ≤ d := by
        refine ⟨?_, ?_⟩ <;>
          · simp only [List.length_cons, List.length_append] at hd; omega
      rw [show (tb 0x40 :: tb 0x00 :: (bt ++ be)) ++ r
          = tb 0x40 :: (tb 0x00 :: (bt ++ (be ++ r))) from by simp]
      rw [decTable]
      simp only [if_true, tb_val 0x40 (by decide), if_pos rfl,
        expectByte_eq 0x00 (by decide) (bt ++ (be ++ r)),
        decTabletype_complete bt tt (be ++ r) htt,
        decExpr_completeD d be e r hlt.2 he]

theorem decGlobal_completeD [authority : BinaryAuthority] : CompleteD Bglobal decGlobal := by
  intro d b g r hd h
  cases h with
  | mk bg be gt e hg he =>
      have hlt : be.length ≤ d := by
        simp only [List.length_append] at hd; omega
      rw [show bg ++ be ++ r = bg ++ (be ++ r) from by simp]
      simp only [decGlobal, decGlobaltype_complete bg gt (be ++ r) hg,
        decExpr_completeD d be e r hlt he]

theorem decFunc_completeD [authority : BinaryAuthority] : CompleteD Bfunc decFunc := by
  intro d b c r hd h
  cases h with
  | mk bl be locss e hlocs he hlen =>
      have hlt : bl.length ≤ d ∧ be.length ≤ d := by
        refine ⟨?_, ?_⟩ <;>
          · simp only [List.length_append] at hd; omega
      rw [show bl ++ be ++ r = bl ++ (be ++ r) from by simp]
      simp only [decFunc,
        decList_completeD (CompleteD.of_complete decLocals_complete) d bl locss
          (be ++ r) hlt.1 hlocs,
        if_pos hlen, decExpr_completeD d be e r hlt.2 he]

theorem decCode_completeD [authority : BinaryAuthority] : CompleteD Bcode decCode := by
  intro d b c r hd h
  cases h with
  | mk =>
      rename_i blen bs len hlen hplen hfunc
      have hlt : bs.length ≤ d := by
        simp only [List.length_append] at hd; omega
      have htake : (bs ++ r).take len.val = bs := by rw [hplen]; exact takeLeft bs r
      have hdrop : (bs ++ r).drop len.val = r := by rw [hplen]; exact dropLeft bs r
      have hf : decFunc d bs = .ok (c, []) := by
        have := decFunc_completeD d bs c [] hlt hfunc
        simpa using this
      rw [show blen ++ bs ++ r = blen ++ (bs ++ r) from by simp, decCode]
      simp only [decU32_complete blen len (bs ++ r) hlen, htake, hdrop, ← hplen,
        if_pos rfl, hf, List.isEmpty_nil, if_true]

/-! ## Element and data segments

The eight `Belem` tags and the three `Bdata` tags are `Bu32`s, so a non-minimal
encoding of the tag is accepted here exactly as it is for an opcode selector. -/

theorem decElem_completeD [authority : BinaryAuthority] : CompleteD Belem decElem := by
  intro d b el r hd h
  cases h with
  | activeFuncrefZero bt be by' e ys x htag hexp hlist hx0 =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : be.length ≤ d := by
        simp only [List.length_append] at hd; omega
      have hx : (⟨0, two_pow_pos 32⟩ : TableIdx) = x := Subtype.ext hx0.symm
      rw [show bt ++ be ++ by' ++ r = bt ++ (be ++ (by' ++ r)) from by simp, decElem]
      simp only [decU32_complete bt v (be ++ (by' ++ r)) hv, hvk,
        decExpr_completeD d be e (by' ++ r) hl hexp,
        decList_complete decIdx_complete by' ys r hlist, hx]
  | passiveFuncref bt bk by' rt ys htag hkind hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      rw [show bt ++ bk ++ by' ++ r = bt ++ (bk ++ (by' ++ r)) from by simp, decElem]
      simp only [decU32_complete bt v (bk ++ (by' ++ r)) hv, hvk,
        decElemkind_complete bk rt (by' ++ r) hkind,
        decList_complete decIdx_complete by' ys r hlist]
  | activeFuncref bt bx be bk by' x e rt ys htag hidx hexp hkind hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : be.length ≤ d := by
        simp only [List.length_append] at hd; omega
      rw [show bt ++ bx ++ be ++ bk ++ by' ++ r
          = bt ++ (bx ++ (be ++ (bk ++ (by' ++ r)))) from by simp, decElem]
      simp only [decU32_complete bt v _ hv, hvk,
        decIdx_complete bx x (be ++ (bk ++ (by' ++ r))) hidx,
        decExpr_completeD d be e (bk ++ (by' ++ r)) hl hexp,
        decElemkind_complete bk rt (by' ++ r) hkind,
        decList_complete decIdx_complete by' ys r hlist]
  | declareFuncref bt bk by' rt ys htag hkind hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      rw [show bt ++ bk ++ by' ++ r = bt ++ (bk ++ (by' ++ r)) from by simp, decElem]
      simp only [decU32_complete bt v (bk ++ (by' ++ r)) hv, hvk,
        decElemkind_complete bk rt (by' ++ r) hkind,
        decList_complete decIdx_complete by' ys r hlist]
  | activeExprZero bt be bl e es x htag hexp hlist hx0 =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : be.length ≤ d ∧ bl.length ≤ d := by
        refine ⟨?_, ?_⟩ <;> · simp only [List.length_append] at hd; omega
      have hx : (⟨0, two_pow_pos 32⟩ : TableIdx) = x := Subtype.ext hx0.symm
      rw [show bt ++ be ++ bl ++ r = bt ++ (be ++ (bl ++ r)) from by simp, decElem]
      simp only [decU32_complete bt v (be ++ (bl ++ r)) hv, hvk,
        decExpr_completeD d be e (bl ++ r) hl.1 hexp,
        decList_completeD decExpr_CompleteD d bl es r hl.2 hlist, hx]
  | passiveExpr bt br bl rt es htag href hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : bl.length ≤ d := by
        simp only [List.length_append] at hd; omega
      rw [show bt ++ br ++ bl ++ r = bt ++ (br ++ (bl ++ r)) from by simp, decElem]
      simp only [decU32_complete bt v (br ++ (bl ++ r)) hv, hvk,
        decReftype_complete br rt (bl ++ r) href,
        decList_completeD decExpr_CompleteD d bl es r hl hlist]
  | activeExpr bt bx be bl x e es htag hidx hexp hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : be.length ≤ d ∧ bl.length ≤ d := by
        refine ⟨?_, ?_⟩ <;> · simp only [List.length_append] at hd; omega
      rw [show bt ++ bx ++ be ++ bl ++ r = bt ++ (bx ++ (be ++ (bl ++ r))) from by simp,
        decElem]
      simp only [decU32_complete bt v _ hv, hvk,
        decIdx_complete bx x (be ++ (bl ++ r)) hidx,
        decExpr_completeD d be e (bl ++ r) hl.1 hexp,
        decList_completeD decExpr_CompleteD d bl es r hl.2 hlist]
  | declareExpr bt br bl rt es htag href hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : bl.length ≤ d := by
        simp only [List.length_append] at hd; omega
      rw [show bt ++ br ++ bl ++ r = bt ++ (br ++ (bl ++ r)) from by simp, decElem]
      simp only [decU32_complete bt v (br ++ (bl ++ r)) hv, hvk,
        decReftype_complete br rt (bl ++ r) href,
        decList_completeD decExpr_CompleteD d bl es r hl hlist]

theorem decData_completeD [authority : BinaryAuthority] : CompleteD Bdata decData := by
  intro d b dt r hd h
  cases h with
  | activeZero bt be bb e bl x htag hexp hlist hx0 =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : be.length ≤ d := by
        simp only [List.length_append] at hd; omega
      have hx : (⟨0, two_pow_pos 32⟩ : MemIdx) = x := Subtype.ext hx0.symm
      rw [show bt ++ be ++ bb ++ r = bt ++ (be ++ (bb ++ r)) from by simp, decData]
      simp only [decU32_complete bt v (be ++ (bb ++ r)) hv, hvk,
        decExpr_completeD d be e (bb ++ r) hl hexp,
        decList_complete readByte_complete bb bl r hlist, hx]
  | passive bt bb bl htag hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      rw [show bt ++ bb ++ r = bt ++ (bb ++ r) from by simp, decData]
      simp only [decU32_complete bt v (bb ++ r) hv, hvk,
        decList_complete readByte_complete bb bl r hlist]
  | active bt bx be bb x e bl htag hidx hexp hlist =>
      obtain ⟨v, hv, hvk⟩ := htag
      have hl : be.length ≤ d := by
        simp only [List.length_append] at hd; omega
      rw [show bt ++ bx ++ be ++ bb ++ r = bt ++ (bx ++ (be ++ (bb ++ r))) from by simp,
        decData]
      simp only [decU32_complete bt v _ hv, hvk,
        decIdx_complete bx x (be ++ (bb ++ r)) hidx,
        decExpr_completeD d be e (bb ++ r) hl hexp,
        decList_complete readByte_complete bb bl r hlist]

/-! ## The module -/

theorem Bsection_shape {α : Type} {G : Bytes → List α → Prop} {N : Nat} {bsec : Bytes}
    {xs : List α} (h : Bsection N G bsec xs) : bsec = [] ∨ ∃ t, bsec = tb N :: t := by
  cases h with
  | absent => exact Or.inl rfl
  | present => rename_i blen bpay len _ _ _; exact Or.inr ⟨blen ++ bpay, rfl⟩

theorem expectBytes_eq : ∀ (ns : List Nat), (∀ n ∈ ns, n < 0x100) → ∀ (r : Bytes),
    expectBytes ns (ns.map tb ++ r) = .ok r := by
  intro ns
  induction ns with
  | nil => intro _ r; rfl
  | cons k ks ih =>
      intro hlt r
      show expectBytes (k :: ks) (tb k :: (ks.map tb ++ r)) = _
      rw [expectBytes, expectByte_eq k (hlt k (by simp))]
      exact ih (fun m hm => hlt m (by simp [hm])) r

/-- The magic number, in the literal shape the module production writes it.
`expectBytes_eq` is the general statement, but its left-hand side carries a
`List.map` that `rw` will not see through in the goal below. -/
theorem expectBytes_magic (r : Bytes) :
    expectBytes [0x00, 0x61, 0x73, 0x6D] ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ r) = .ok r :=
  rfl

/-- The version number, likewise. -/
theorem expectBytes_version (r : Bytes) :
    expectBytes [0x01, 0x00, 0x00, 0x00] ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ r) = .ok r :=
  rfl

/-- A later position of the module production has no more bytes than the whole. -/
theorem segsBytes_suffix_le : ∀ (pre segs : List Seg) (post : Bytes),
    (segsBytes segs post).length ≤ (segsBytes (pre ++ segs) post).length := by
  intro pre
  induction pre with
  | nil => intro segs post; exact Nat.le_refl _
  | cons s rest ih =>
      intro segs post
      have hle := ih segs post
      simp only [List.cons_append, segsBytes, List.length_append]
      omega

/-- The three starred side conditions of the pinned module production are
ACCEPTED by the checker exactly when the grammar's hypotheses hold. -/
theorem finishModule_complete
    (types : List TypeDef) (imports : List Import) (typeidxs : List TypeIdx)
    (tables : List Table) (mems : List Mem) (tags : List Tag) (globals : List Global)
    (exports : List Export) (start : Option Start) (elems : List Elem)
    (n : Option U32) (codes : List Code) (datas : List Data)
    (hcnt : ∀ k : U32, n = some k → k.val = datas.length)
    (hdata : n ≠ none ∨ dataIdxFuncs (List.zipWith (fun (x : TypeIdx) (c : Code) =>
        ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes) = [])
    (hlen : typeidxs.length = codes.length) :
    finishModule types imports typeidxs tables mems tags globals exports start.toList
        elems n.toList codes datas
      = .ok { types := types, imports := imports, tags := tags, globals := globals,
              mems := mems, tables := tables,
              funcs := List.zipWith (fun (x : TypeIdx) (c : Code) =>
                ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes,
              datas := datas, elems := elems, start := start, exports := exports } := by
  have hs : optOf1 start.toList = some start := by cases start <;> rfl
  have hc : optOf1 n.toList = some n := by cases n <;> rfl
  have hside : (cntAgrees n datas.length &&
      cntPresentOrNoData n (List.zipWith (fun (x : TypeIdx) (c : Code) =>
        ({ typeidx := x, locals := c.1, body := c.2 } : Func)) typeidxs codes)) = true := by
    refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
    · cases n with
      | none => rfl
      | some k => exact decide_eq_true (hcnt k rfl)
    · cases n with
      | none =>
          rcases hdata with hne | hemp
          · exact absurd rfl hne
          · show (dataIdxFuncs _).isEmpty = true
            rw [hemp]; rfl
      | some k => rfl
  simp only [finishModule, hs, hc, if_pos hlen, hside, if_true]


/-- **COMPLETENESS OF THE MODULE DECODER.**  Every derivation of the pinned
`Bmodule` is decoded, to the module the derivation produces. -/
theorem decModule_complete [authority : BinaryAuthority]
    (bs : Bytes) (m : Module) (h : Bmodule bs m) :
    decModule bs = .ok m := by
  cases h with
  | mk bmag bver c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ u₀ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ bty bim bfu bta bme btg bgl bex bst bel bdc bco bda types imports typeidxs tables mems tags globals exports start elems n codes datas funcs hmag hver hu₀ hty hu₁ him hu₂ hfu hu₃ hta hu₄ hme hu₅ htg hu₆ hgl hu₇ hex hu₈ hst hu₉ hel hu₁₀ hdc hu₁₁ hco hu₁₂ hda hu₁₃ hcnt hdatai hlenc hzip =>
      cases hmag
      cases hver
      subst hzip
      obtain ⟨k₀, hk₀⟩ := hu₀
      have hcr₀ : CustRun c₀ := ⟨k₀, u₀, hk₀⟩
      obtain ⟨k₁, hk₁⟩ := hu₁
      have hcr₁ : CustRun c₁ := ⟨k₁, u₁, hk₁⟩
      obtain ⟨k₂, hk₂⟩ := hu₂
      have hcr₂ : CustRun c₂ := ⟨k₂, u₂, hk₂⟩
      obtain ⟨k₃, hk₃⟩ := hu₃
      have hcr₃ : CustRun c₃ := ⟨k₃, u₃, hk₃⟩
      obtain ⟨k₄, hk₄⟩ := hu₄
      have hcr₄ : CustRun c₄ := ⟨k₄, u₄, hk₄⟩
      obtain ⟨k₅, hk₅⟩ := hu₅
      have hcr₅ : CustRun c₅ := ⟨k₅, u₅, hk₅⟩
      obtain ⟨k₆, hk₆⟩ := hu₆
      have hcr₆ : CustRun c₆ := ⟨k₆, u₆, hk₆⟩
      obtain ⟨k₇, hk₇⟩ := hu₇
      have hcr₇ : CustRun c₇ := ⟨k₇, u₇, hk₇⟩
      obtain ⟨k₈, hk₈⟩ := hu₈
      have hcr₈ : CustRun c₈ := ⟨k₈, u₈, hk₈⟩
      obtain ⟨k₉, hk₉⟩ := hu₉
      have hcr₉ : CustRun c₉ := ⟨k₉, u₉, hk₉⟩
      obtain ⟨k₁₀, hk₁₀⟩ := hu₁₀
      have hcr₁₀ : CustRun c₁₀ := ⟨k₁₀, u₁₀, hk₁₀⟩
      obtain ⟨k₁₁, hk₁₁⟩ := hu₁₁
      have hcr₁₁ : CustRun c₁₁ := ⟨k₁₁, u₁₁, hk₁₁⟩
      obtain ⟨k₁₂, hk₁₂⟩ := hu₁₂
      have hcr₁₂ : CustRun c₁₂ := ⟨k₁₂, u₁₂, hk₁₂⟩
      obtain ⟨k₁₃, hk₁₃⟩ := hu₁₃
      have hcr₁₃ : CustRun c₁₃ := ⟨k₁₃, u₁₃, hk₁₃⟩
      have hstS : Bsection 8 Bstart bst start.toList := by
        cases hst with
        | absent => rename_i hx; exact hx
        | present => rename_i s hx; exact hx
      have hdcS : Bsection 12 Bdatacnt bdc n.toList := by
        cases hdc with
        | absent => rename_i hx; exact hx
        | present => rename_i kk hx; exact hx
      have hseg1 : SegOk ⟨1, c₀, bty⟩ :=
        ⟨hcr₀, (by decide : (1:Nat) < 0x100), (by decide : (1:Nat) ≠ 0),
          Bsection_shape hty⟩
      have hseg2 : SegOk ⟨2, c₁, bim⟩ :=
        ⟨hcr₁, (by decide : (2:Nat) < 0x100), (by decide : (2:Nat) ≠ 0),
          Bsection_shape him⟩
      have hseg3 : SegOk ⟨3, c₂, bfu⟩ :=
        ⟨hcr₂, (by decide : (3:Nat) < 0x100), (by decide : (3:Nat) ≠ 0),
          Bsection_shape hfu⟩
      have hseg4 : SegOk ⟨4, c₃, bta⟩ :=
        ⟨hcr₃, (by decide : (4:Nat) < 0x100), (by decide : (4:Nat) ≠ 0),
          Bsection_shape hta⟩
      have hseg5 : SegOk ⟨5, c₄, bme⟩ :=
        ⟨hcr₄, (by decide : (5:Nat) < 0x100), (by decide : (5:Nat) ≠ 0),
          Bsection_shape hme⟩
      have hseg6 : SegOk ⟨13, c₅, btg⟩ :=
        ⟨hcr₅, (by decide : (13:Nat) < 0x100), (by decide : (13:Nat) ≠ 0),
          Bsection_shape htg⟩
      have hseg7 : SegOk ⟨6, c₆, bgl⟩ :=
        ⟨hcr₆, (by decide : (6:Nat) < 0x100), (by decide : (6:Nat) ≠ 0),
          Bsection_shape hgl⟩
      have hseg8 : SegOk ⟨7, c₇, bex⟩ :=
        ⟨hcr₇, (by decide : (7:Nat) < 0x100), (by decide : (7:Nat) ≠ 0),
          Bsection_shape hex⟩
      have hseg9 : SegOk ⟨8, c₈, bst⟩ :=
        ⟨hcr₈, (by decide : (8:Nat) < 0x100), (by decide : (8:Nat) ≠ 0),
          Bsection_shape hstS⟩
      have hseg10 : SegOk ⟨9, c₉, bel⟩ :=
        ⟨hcr₉, (by decide : (9:Nat) < 0x100), (by decide : (9:Nat) ≠ 0),
          Bsection_shape hel⟩
      have hseg11 : SegOk ⟨12, c₁₀, bdc⟩ :=
        ⟨hcr₁₀, (by decide : (12:Nat) < 0x100), (by decide : (12:Nat) ≠ 0),
          Bsection_shape hdcS⟩
      have hseg12 : SegOk ⟨10, c₁₁, bco⟩ :=
        ⟨hcr₁₁, (by decide : (10:Nat) < 0x100), (by decide : (10:Nat) ≠ 0),
          Bsection_shape hco⟩
      have hseg13 : SegOk ⟨11, c₁₂, bda⟩ :=
        ⟨hcr₁₂, (by decide : (11:Nat) < 0x100), (by decide : (11:Nat) ≠ 0),
          Bsection_shape hda⟩
      have hok1 : ∀ t ∈ ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hseg1
        · exact hseg2
        · exact hseg3
        · exact hseg4
        · exact hseg5
        · exact hseg6
        · exact hseg7
        · exact hseg8
        · exact hseg9
        · exact hseg10
        · exact hseg11
        · exact hseg12
        · exact hseg13
      have hok2 : ∀ t ∈ ([⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok1 t (List.mem_cons_of_mem _ ht)
      have hok3 : ∀ t ∈ ([⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok2 t (List.mem_cons_of_mem _ ht)
      have hok4 : ∀ t ∈ ([⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok3 t (List.mem_cons_of_mem _ ht)
      have hok5 : ∀ t ∈ ([⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok4 t (List.mem_cons_of_mem _ ht)
      have hok6 : ∀ t ∈ ([⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok5 t (List.mem_cons_of_mem _ ht)
      have hok7 : ∀ t ∈ ([⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok6 t (List.mem_cons_of_mem _ ht)
      have hok8 : ∀ t ∈ ([⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok7 t (List.mem_cons_of_mem _ ht)
      have hok9 : ∀ t ∈ ([⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok8 t (List.mem_cons_of_mem _ ht)
      have hok10 : ∀ t ∈ ([⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok9 t (List.mem_cons_of_mem _ ht)
      have hok11 : ∀ t ∈ ([⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok10 t (List.mem_cons_of_mem _ ht)
      have hok12 : ∀ t ∈ ([⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok11 t (List.mem_cons_of_mem _ ht)
      have hok13 : ∀ t ∈ ([⟨11, c₁₂, bda⟩] : List Seg), SegOk t := fun t ht => hok12 t (List.mem_cons_of_mem _ ht)
      have hok14 : ∀ t ∈ ([] : List Seg), SegOk t := fun t ht => absurd ht (by simp)
      have hne1 : ∀ t ∈ ([⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 1 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne2 : ∀ t ∈ ([⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 2 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne3 : ∀ t ∈ ([⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 3 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne4 : ∀ t ∈ ([⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 4 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne5 : ∀ t ∈ ([⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 5 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne6 : ∀ t ∈ ([⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 13 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne7 : ∀ t ∈ ([⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 6 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      have hne8 : ∀ t ∈ ([⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 7 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp
      have hne9 : ∀ t ∈ ([⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 8 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> simp
      have hne10 : ∀ t ∈ ([⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 9 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl <;> simp
      have hne11 : ∀ t ∈ ([⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 12 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> simp
      have hne12 : ∀ t ∈ ([⟨11, c₁₂, bda⟩] : List Seg), t.id ≠ 10 := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl <;> simp
      have hne13 : ∀ t ∈ ([] : List Seg), t.id ≠ 11 := by
        intro t ht; exact absurd ht (by simp)
      have hshape : [tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ [tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++
          c₀ ++ bty ++ c₁ ++ bim ++ c₂ ++ bfu ++ c₃ ++ bta ++ c₄ ++ bme ++ c₅ ++ btg ++ c₆ ++ bgl ++ c₇ ++ bex ++ c₈ ++ bst ++ c₉ ++ bel ++ c₁₀ ++ bdc ++ c₁₁ ++ bco ++ c₁₂ ++ bda ++ c₁₃
          = ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)) := by
        simp [segsBytes]
      rw [hshape, decModule]
      simp only [expectBytes_magic, expectBytes_version]
      have hX1 : decCustoms ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length (segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃) = .ok (strip ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃) :=
        decCustoms_segs ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ hok1 hcr₁₃ ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega)
      obtain ⟨Y1, hs1, hX2⟩ := step_complete (decList_completeD (CompleteD.of_complete decType_complete)) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 1 c₀ bty ([⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ types (segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)
        hok1 hcr₁₃ hne1 hty (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX1
      simp only [hs1]
      obtain ⟨Y2, hs2, hX3⟩ := step_complete (decList_completeD (CompleteD.of_complete decImport_complete)) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 2 c₁ bim ([⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ imports Y1
        hok2 hcr₁₃ hne2 him (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX2
      simp only [hs2]
      obtain ⟨Y3, hs3, hX4⟩ := step_complete (decList_completeD (CompleteD.of_complete decIdx_complete)) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 3 c₂ bfu ([⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ typeidxs Y2
        hok3 hcr₁₃ hne3 hfu (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX3
      simp only [hs3]
      obtain ⟨Y4, hs4, hX5⟩ := step_complete (decList_completeD decTable_completeD) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 4 c₃ bta ([⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ tables Y3
        hok4 hcr₁₃ hne4 hta (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX4
      simp only [hs4]
      obtain ⟨Y5, hs5, hX6⟩ := step_complete (decList_completeD (CompleteD.of_complete decMem_complete)) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 5 c₄ bme ([⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ mems Y4
        hok5 hcr₁₃ hne5 hme (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX5
      simp only [hs5]
      obtain ⟨Y6, hs6, hX7⟩ := step_complete (decList_completeD (CompleteD.of_complete decTag_complete)) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 13 c₅ btg ([⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ tags Y5
        hok6 hcr₁₃ hne6 htg (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX6
      simp only [hs6]
      obtain ⟨Y7, hs7, hX8⟩ := step_complete (decList_completeD decGlobal_completeD) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 6 c₆ bgl ([⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ globals Y6
        hok7 hcr₁₃ hne7 hgl (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX7
      simp only [hs7]
      obtain ⟨Y8, hs8, hX9⟩ := step_complete (decList_completeD (CompleteD.of_complete decExport_complete)) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 7 c₇ bex ([⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ exports Y7
        hok8 hcr₁₃ hne8 hex (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX8
      simp only [hs8]
      obtain ⟨Y9, hs9, hX10⟩ := step_complete (CompleteD.of_complete decStart_complete) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 8 c₈ bst ([⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ start.toList Y8
        hok9 hcr₁₃ hne9 hstS (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX9
      simp only [hs9]
      obtain ⟨Y10, hs10, hX11⟩ := step_complete (decList_completeD decElem_completeD) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 9 c₉ bel ([⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ elems Y9
        hok10 hcr₁₃ hne10 hel (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX10
      simp only [hs10]
      obtain ⟨Y11, hs11, hX12⟩ := step_complete (CompleteD.of_complete decDatacnt_complete) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 12 c₁₀ bdc ([⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃ n.toList Y10
        hok11 hcr₁₃ hne11 hdcS (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX11
      simp only [hs11]
      obtain ⟨Y12, hs12, hX13⟩ := step_complete (decList_completeD decCode_completeD) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 10 c₁₁ bco ([⟨11, c₁₂, bda⟩] : List Seg) c₁₃ codes Y11
        hok12 hcr₁₃ hne12 hco (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX12
      simp only [hs12]
      obtain ⟨Y13, hs13, hX14⟩ := step_complete (decList_completeD decData_completeD) ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length ([tb 0x00, tb 0x61, tb 0x73, tb 0x6D] ++ ([tb 0x01, tb 0x00, tb 0x00, tb 0x00] ++ segsBytes ([⟨1, c₀, bty⟩, ⟨2, c₁, bim⟩, ⟨3, c₂, bfu⟩, ⟨4, c₃, bta⟩, ⟨5, c₄, bme⟩, ⟨13, c₅, btg⟩, ⟨6, c₆, bgl⟩, ⟨7, c₇, bex⟩, ⟨8, c₈, bst⟩, ⟨9, c₉, bel⟩, ⟨12, c₁₀, bdc⟩, ⟨10, c₁₁, bco⟩, ⟨11, c₁₂, bda⟩] : List Seg) c₁₃)).length 11 c₁₂ bda ([] : List Seg) c₁₃ datas Y12
        hok13 hcr₁₃ hne13 hda (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) (by simp only [segsBytes, List.length_append, List.length_cons, List.length_nil]; omega) hX13
      simp only [hs13]
      simp only [hX14, strip, List.isEmpty_nil, if_true]
      exact finishModule_complete types imports typeidxs tables mems tags globals exports
        start elems n codes datas hcnt hdatai hlenc

/-- Completeness of the amended decoder against the exact amended grammar. -/
theorem decModule_completeA (bs : Bytes) (m : Module) (h : BmoduleA bs m) :
    decModuleA bs = .ok m :=
  @decModule_complete amendedBinaryAuthority bs m h

end WasmGemmGnaf.Wasm.Core.Decode
