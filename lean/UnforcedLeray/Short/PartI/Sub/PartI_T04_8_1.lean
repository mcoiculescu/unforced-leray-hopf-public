import UnforcedLeray.Short.PartI.Sub.PartI_T04_8

/-!
# Decomposition of `APEllipticA` (`PartI:T04/8/1`)

Source: `the November 2 reference manuscript` lines 285-287.
The cell identity is a finite sum over order-`j` words of the per-word identity; the per-word
integrability and per-word identity are the two analytic lemmas.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Per-word integrability (lines 285-287): for `g = ∂_w f` (smooth, periodic, divergence free,
bounded `L²` derivatives) both `Σ_k |∇ g_k|²` and `(∂_w curl f)²` are integrable on the cell.
Route: `|∂_q g_k|, |∂_η g_k| ≤ ‖D^{j+1} f‖` and `|∂_w curl f| ≤ 2‖D^{j+1} f‖`-type bounds with
`APEllipticData` integrability of `‖D^i f‖²`. -/
def APEllipticAInt : Prop :=
  ∀ (j : ℕ) (c : ℝ) (f : Plane → Vec), APEllipticData c f → ∀ w ∈ wordsOfLength j,
    IntegrableOn (fun z => ∑ k : Fin 2,
      (Cyl.partialQ (wordComp w f k) z ^ 2 + Cyl.partialEta (wordComp w f k) z ^ 2)) (Cyl.cell c) ∧
    IntegrableOn (fun z => B0151.derivWord w (Cyl.curl f) z ^ 2) (Cyl.cell c)

/-- Per-word cell identity (lines 285-287): `∫_cell Σ_k |∇ ∂_w f_k|² = ∫_cell (∂_w curl f)²`.
Route: `∂_w` commutes with `curl`, `div`; pointwise
`Σ_k|∇g_k|² = (curl g)² + (div g)² + 2(∂_q g_η ∂_η g_q - ∂_q g_q ∂_η g_η)` (ring identity); the
integral of the last bracket vanishes (IBP in `q` periodic via `Sob.integral_cylCell_fderiv_eq_zero`;
in `η` via `integral_eq_zero_of_hasDerivAt_of_integrable` on each slice, or cutoff `R → ∞`). -/
def APEllipticAEq : Prop :=
  ∀ (j : ℕ) (c : ℝ) (f : Plane → Vec), APEllipticData c f → ∀ w ∈ wordsOfLength j,
    ∫ z in Cyl.cell c, ∑ k : Fin 2,
      (Cyl.partialQ (wordComp w f k) z ^ 2 + Cyl.partialEta (wordComp w f k) z ^ 2) =
    ∫ z in Cyl.cell c, B0151.derivWord w (Cyl.curl f) z ^ 2

theorem apEllipticA_of (h1 : APEllipticAInt) (h2 : APEllipticAEq) : APEllipticA := by
  intro j c f hf
  refine ⟨?_, ?_, ?_⟩
  · unfold wordGradSq
    exact integrable_finset_sum _ (fun w hw => (h1 j c f hf w hw).1)
  · unfold wordCurlSq
    exact integrable_finset_sum _ (fun w hw => (h1 j c f hf w hw).2)
  · unfold wordGradSq wordCurlSq
    rw [integral_finset_sum _ (fun w hw => (h1 j c f hf w hw).1),
      integral_finset_sum _ (fun w hw => (h1 j c f hf w hw).2)]
    exact Finset.sum_congr rfl (fun w hw => h2 j c f hf w hw)

end UnforcedLeray.Short.PartI
