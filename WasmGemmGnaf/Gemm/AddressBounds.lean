import WasmGemmGnaf.Gemm.Classify

set_option autoImplicit false

/-!
# Address bounds carried by a valid GEMM descriptor

These lemmas expose the mathematical-integer bounds already present in
`DescriptorWellFormed`.  They are the compiler-facing facts needed before an
effective address may be converted to wasm32: the complete element byte range
lies inside the raw invocation window, and a lawful wasm32 invocation therefore
cannot wrap.
-/

namespace WasmGemmGnaf.Gemm

namespace Descriptor

variable {P : Wasm.Profile}

/-- Every addressed A element lies inside the invocation window, before any
machine-width conversion. -/
theorem aBytes_in_window (d : Descriptor P) {x : Index}
    (hx : x.Mem d.body.shapeA) :
    0 ≤ d.body.aView.addrOf d.body.transposeA x ∧
      d.body.aView.addrOf d.body.transposeA x +
          (d.body.aKind.byteWidth : Int) ≤ (d.window.len : Int) := by
  obtain ⟨hlo, hhi⟩ := d.wellFormed.layoutA.elementsInInterval x hx
  have hend := d.wellFormed.layoutA.endpointsRepresentable
  omega

/-- Every addressed B element lies inside the invocation window, before any
machine-width conversion. -/
theorem bBytes_in_window (d : Descriptor P) {x : Index}
    (hx : x.Mem d.body.shapeB) :
    0 ≤ d.body.bView.addrOf d.body.transposeB x ∧
      d.body.bView.addrOf d.body.transposeB x +
          (d.body.bKind.byteWidth : Int) ≤ (d.window.len : Int) := by
  obtain ⟨hlo, hhi⟩ := d.wellFormed.layoutB.elementsInInterval x hx
  have hend := d.wellFormed.layoutB.endpointsRepresentable
  omega

/-- Every addressed C element lies inside the invocation window, before any
machine-width conversion. -/
theorem cBytes_in_window (d : Descriptor P) {x : Index}
    (hx : x.Mem d.body.shapeC) :
    0 ≤ d.body.cView.addrOf false x ∧
      d.body.cView.addrOf false x + (d.body.cKind.byteWidth : Int) ≤
        (d.window.len : Int) := by
  obtain ⟨hlo, hhi⟩ := d.wellFormed.layoutC.elementsInInterval x hx
  have hend := d.wellFormed.layoutC.endpointsRepresentable
  omega

end Descriptor

namespace ValidInvocation

variable {P : Wasm.Profile}

/-- A lawful valid invocation's complete A element byte range is representable
as a wasm32 address. -/
theorem aBytes_in_wasm32 (inv : ValidInvocation P)
    (hlawful : RawInvocationLawful P inv.raw) {x : Index}
    (hx : x.Mem inv.descriptor.body.shapeA) :
    0 ≤ (inv.descriptor.window.ptr : Int) +
        inv.descriptor.body.aView.addrOf inv.descriptor.body.transposeA x ∧
      (inv.descriptor.window.ptr : Int) +
          inv.descriptor.body.aView.addrOf inv.descriptor.body.transposeA x +
          (inv.descriptor.body.aKind.byteWidth : Int) ≤ 2 ^ 32 := by
  obtain ⟨hlo, hhi⟩ := inv.descriptor.aBytes_in_window hx
  have hptr := congrArg MemoryWindow.ptr inv.windowMatches
  have hlen := congrArg MemoryWindow.len inv.windowMatches
  have hrange := hlawful.2.1
  have hbits : P.addressBits = 32 := P.lawful.addressBits
  rw [hbits] at hrange
  simp only [windowOf] at hptr hlen
  omega

/-- A lawful valid invocation's complete B element byte range is representable
as a wasm32 address. -/
theorem bBytes_in_wasm32 (inv : ValidInvocation P)
    (hlawful : RawInvocationLawful P inv.raw) {x : Index}
    (hx : x.Mem inv.descriptor.body.shapeB) :
    0 ≤ (inv.descriptor.window.ptr : Int) +
        inv.descriptor.body.bView.addrOf inv.descriptor.body.transposeB x ∧
      (inv.descriptor.window.ptr : Int) +
          inv.descriptor.body.bView.addrOf inv.descriptor.body.transposeB x +
          (inv.descriptor.body.bKind.byteWidth : Int) ≤ 2 ^ 32 := by
  obtain ⟨hlo, hhi⟩ := inv.descriptor.bBytes_in_window hx
  have hptr := congrArg MemoryWindow.ptr inv.windowMatches
  have hlen := congrArg MemoryWindow.len inv.windowMatches
  have hrange := hlawful.2.1
  have hbits : P.addressBits = 32 := P.lawful.addressBits
  rw [hbits] at hrange
  simp only [windowOf] at hptr hlen
  omega

/-- A lawful valid invocation's complete C element byte range is representable
as a wasm32 address. -/
theorem cBytes_in_wasm32 (inv : ValidInvocation P)
    (hlawful : RawInvocationLawful P inv.raw) {x : Index}
    (hx : x.Mem inv.descriptor.body.shapeC) :
    0 ≤ (inv.descriptor.window.ptr : Int) +
        inv.descriptor.body.cView.addrOf false x ∧
      (inv.descriptor.window.ptr : Int) +
          inv.descriptor.body.cView.addrOf false x +
          (inv.descriptor.body.cKind.byteWidth : Int) ≤ 2 ^ 32 := by
  obtain ⟨hlo, hhi⟩ := inv.descriptor.cBytes_in_window hx
  have hptr := congrArg MemoryWindow.ptr inv.windowMatches
  have hlen := congrArg MemoryWindow.len inv.windowMatches
  have hrange := hlawful.2.1
  have hbits : P.addressBits = 32 := P.lawful.addressBits
  rw [hbits] at hrange
  simp only [windowOf] at hptr hlen
  omega

end ValidInvocation

end WasmGemmGnaf.Gemm
