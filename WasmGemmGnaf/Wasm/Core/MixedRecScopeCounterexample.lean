/-
  Kernel witness for DEV-015.  The byte-identical pinned recursive-type
  validity relation permits an ordinary `cons` proof followed by `_rec2` on
  the remaining suffix.  The suffix interprets `REC 0` relative to itself;
  semantic closing later interprets the same use relative to the full group.

  The amended hierarchy excludes the mixed proof structurally.  This file
  deliberately states the witness only over the pinned authority relation.
-/
import WasmGemmGnaf.Wasm.Core.SubtypeSound

set_option autoImplicit false

namespace WasmGemmGnaf.Wasm.Core

private def mixedScopeStruct : SubType :=
  .sub (some .final) .nil (.struct .nil)

private def mixedScopeFunc0 : SubType :=
  .sub (some .final) .nil (.func .nil .nil)

private def mixedScopeFunc1 : SubType :=
  .sub (some .final) (.cons (.recu 0) .nil) (.func .nil .nil)

private def mixedScopeQt : RecType :=
  .recr (.ofList [mixedScopeStruct, mixedScopeFunc0, mixedScopeFunc1])

private def mixedScopeStructDt : DefType := .defd mixedScopeQt 0
private def mixedScopeFuncDt : DefType := .defd mixedScopeQt 2

private theorem mixedScopeEmptyResultOk (C : Context) : Resulttype_ok C [] :=
  .mk (fun t ht => by simp at ht)

private theorem mixedScopeEmptyFuncOk (C : Context) :
    Comptype_ok C (.func .nil .nil) :=
  .func (mixedScopeEmptyResultOk C) (mixedScopeEmptyResultOk C)

private theorem mixedScopeEmptyFuncSub (C : Context) :
    Comptype_sub C (.func .nil .nil) (.func .nil .nil) :=
  .func (.mk rfl (fun _ _ _ h _ => nomatch h))
    (.mk rfl (fun _ _ _ h _ => nomatch h))

private theorem mixedScopeStructOk (C : Context) :
    Subtype_ok C mixedScopeStruct (TypeIdx.ofNat 0) := by
  apply Subtype_ok.mk (xs := []) (cts' := [])
  · decide
  · rfl
  · intro i x ct hx _
    simp at hx
  · exact .struct (fun _ h => nomatch h)
  · intro ct h
    nomatch h

private theorem mixedScopeTailRec2 :
    Rectype_ok2
      (Context.empty.withRecs [mixedScopeFunc0, mixedScopeFunc1])
      (.recr (.ofList [mixedScopeFunc0, mixedScopeFunc1]))
      (TypeIdx.ofNat 1) 0 := by
  apply Rectype_ok2.cons
  · apply Subtype_ok2.mk (cts' := [])
    · decide
    · rfl
    · intro i tu ct htu _
      simp [TypeUses.toList] at htu
    · exact mixedScopeEmptyFuncOk _
    · intro ct h
      nomatch h
  · apply Rectype_ok2.cons
    · apply Subtype_ok2.mk (cts' := [.func .nil .nil])
      · decide
      · rfl
      · intro i tu ct htu hct
        have hi : i = 0 := by
          cases i with
          | zero => rfl
          | succ i => simp [TypeUses.toList] at htu
        subst i
        have htu' : tu = .recu 0 := (Option.some.inj htu).symm
        subst tu
        have hct' : ct = .func .nil .nil := (Option.some.inj hct).symm
        subst ct
        exact ⟨by decide, some .final, .nil, by
          simp [Context.unrollHt, Context.withRecs, mixedScopeFunc0]⟩
      · exact mixedScopeEmptyFuncOk _
      · intro ct hct
        have hct' : ct = .func .nil .nil := by simpa using hct
        subst ct
        exact mixedScopeEmptyFuncSub _
    · exact .empty

private theorem mixedScopeQtOk :
    Rectype_ok Context.empty mixedScopeQt (TypeIdx.ofNat 0) := by
  apply Rectype_ok.cons
  · exact mixedScopeStructOk _
  · apply Rectype_ok.rec2
    simpa [mixedScopeQt, mixedScopeStruct, SubTypes.toList_ofList] using
      mixedScopeTailRec2

private theorem mixedScopeStructDtOk :
    Deftype_ok Context.empty mixedScopeStructDt :=
  .mk mixedScopeQtOk (by decide)

private theorem mixedScopeFuncDtOk :
    Deftype_ok Context.empty mixedScopeFuncDt :=
  .mk mixedScopeQtOk (by decide)

private theorem mixedScopeStructExpand :
    Expand mixedScopeStructDt (.struct .nil) :=
  .mk (by decide)

private theorem mixedScopeFuncExpand :
    Expand mixedScopeFuncDt (.func .nil .nil) :=
  .mk (by decide)

private theorem mixedScopeFuncUnroll :
    unrollDt mixedScopeFuncDt = some
      (.sub (some .final) (.cons (.defd mixedScopeStructDt) .nil)
        (.func .nil .nil)) := by
  decide

/-- The pinned mixed recursive-scope derivation crosses from the function
family to the structure family, while the executable lattice rejects the two
abstract endpoints for every fuel.  AMD-015 removes this proof-internal edge
from the sole amended hierarchy. -/
theorem heapDecision_not_complete_of_mixed_rec_scope :
    Heaptype_sub Context.empty (.abs .nofunc) (.abs .struct) ∧
      ∀ n, decHeaptypeSubN Context.empty n (.abs .nofunc) (.abs .struct) = false := by
  have hfunc : Heaptype_sub Context.empty
      (.use (.defd mixedScopeFuncDt)) (.abs .func) :=
    .func mixedScopeFuncExpand
  have hbottom : Heaptype_sub Context.empty (.abs .nofunc)
      (.use (.defd mixedScopeFuncDt)) :=
    .nofunc hfunc
  have hsuper : Heaptype_sub Context.empty
      (.use (.defd mixedScopeFuncDt)) (.use (.defd mixedScopeStructDt)) := by
    exact .def_ (.super mixedScopeFuncUnroll (i := 0) (by rfl) .refl)
  have hstruct : Heaptype_sub Context.empty
      (.use (.defd mixedScopeStructDt)) (.abs .struct) :=
    .struct mixedScopeStructExpand
  exact ⟨.trans (.typeuse (.deftype mixedScopeFuncDtOk)) hbottom
      (.trans (.typeuse (.deftype mixedScopeStructDtOk)) hsuper hstruct),
    fun _ => rfl⟩

end WasmGemmGnaf.Wasm.Core
