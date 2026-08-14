/-
  A proved lower bound on charged operations for bilinear matrix-multiplication
  schemes, under the release objective's weight-one accounting.

  SCOPE — read this before citing anything here.

  This file proves a *partial* universal lower bound: it quantifies over bilinear
  schemes, NOT over all WebAssembly byte modules.  It is therefore a step toward
  the obligation UOR-GNAF §19.3 calls "a universal lower bound attained", and it is
  NOT that obligation discharged.  `Universal.universal_sublevel_coverage` and
  `Artifact.released_wasm_gemm_gnaf_global_optimal` remain absent.

  What it establishes is deliberately narrower. The objective charges
  multiplications *and* additions at weight one, and the theorem below proves
  `T ≥ r + 18` for every modeled bilinear scheme. The naive scheme witnesses
  equality at `r = 27`. This does not prove naive minimality across lower-rank
  schemes and does not show that resolving the open tensor-rank interval is
  irrelevant to the release theorem.
-/
import WasmGemmGnaf.Cost.Objective

set_option autoImplicit false

namespace WasmGemmGnaf.Universal

/-- Every entry of a list of positive naturals contributes at least one to the sum,
so the sum dominates the length. -/
theorem length_le_sum : ∀ {l : List Nat}, (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum
  | [], _ => Nat.le_refl 0
  | a :: t, h => by
      have ha : 1 ≤ a := h a (by simp)
      have ht : t.length ≤ t.sum :=
        length_le_sum (fun x hx => h x (by simp [hx]))
      simp only [List.length_cons, List.sum_cons]
      omega

/--
The charged-operation accounting of a bilinear scheme for `3 × 3` matrix
multiplication, in the release cost model.
-/
structure BilinearScheme where
  pSupport : List Nat
  wSupport : List Nat
  uSupport : List Nat
  pLength : pSupport.length = wSupport.length
  uLength : uSupport.length = pSupport.length
  pPos : ∀ x ∈ pSupport, 1 ≤ x
  wPos : ∀ x ∈ wSupport, 1 ≤ x

namespace BilinearScheme

/-- The number of multiplications the scheme performs. -/
def rank (s : BilinearScheme) : Nat := s.pSupport.length

/-- Total charged operations: `r` multiplications, input-side additions `Σ(p−1)`
and `Σ(w−1)`, and reconstruction additions `Σu − 9`.  Stated additively to avoid
truncated natural subtraction. -/
def ChargedOps (s : BilinearScheme) (total : Nat) : Prop :=
  total + s.rank + 9 = s.pSupport.sum + s.wSupport.sum + s.uSupport.sum

/-- Each of the nine outputs of `3 × 3` matrix multiplication is a bilinear form of
rank three, so at least three distinct products feed it; summing over the nine
outputs, the reconstruction supports total at least `27`. -/
def OutputsAreRankThree (s : BilinearScheme) : Prop := 27 ≤ s.uSupport.sum

/--
**Charged-operation lower bound for bilinear `3 × 3` schemes.**  `T ≥ r + 18`,
uniformly in the number of multiplications `r`.

The naive algorithm witnesses equality (`r = 27`, `18` additions, `45` charged
operations), so the formula cannot be uniformly strengthened at rank 27. For
contrast, Laderman's particular `23`-multiplication scheme uses `98` additions:
`121` charged operations against naive's `45`. Neither fact excludes a different
lower-rank scheme with total cost below `45`.
-/
theorem chargedOps_lower_bound
    (s : BilinearScheme) (total : Nat)
    (hcharge : s.ChargedOps total)
    (hout : s.OutputsAreRankThree) :
    s.rank + 18 ≤ total := by
  have hp : s.rank ≤ s.pSupport.sum := length_le_sum s.pPos
  have hw : s.rank ≤ s.wSupport.sum := by
    have h : s.wSupport.length ≤ s.wSupport.sum := length_le_sum s.wPos
    rw [rank, s.pLength]; exact h
  unfold ChargedOps at hcharge
  unfold OutputsAreRankThree at hout
  omega

/-- The naive algorithm: `27` products, every linear form a single entry, every
product feeding exactly one output. -/
def naive : BilinearScheme where
  pSupport := List.replicate 27 1
  wSupport := List.replicate 27 1
  uSupport := List.replicate 27 1
  pLength := by simp
  uLength := by simp
  pPos := by intro x hx; simp [List.eq_of_mem_replicate hx]
  wPos := by intro x hx; simp [List.eq_of_mem_replicate hx]

theorem naive_rank : naive.rank = 27 := by simp [rank, naive]

theorem naive_outputsAreRankThree : naive.OutputsAreRankThree := by
  simp [OutputsAreRankThree, naive]

/-- The naive algorithm performs `45` charged operations. -/
theorem naive_chargedOps : naive.ChargedOps 45 := by
  simp [ChargedOps, naive, rank]

/-- The bound is **attained**, so it cannot be improved as a function of rank. -/
theorem naive_attains_bound : naive.rank + 18 = 45 := by
  rw [naive_rank]

end BilinearScheme

end WasmGemmGnaf.Universal
