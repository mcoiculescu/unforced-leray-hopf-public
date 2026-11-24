import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_5_3_1

/-!
# `PartIII-a:T21/2/2/3/5/3/1`, leaf `WPRSplit` (abstract measure theory)

Source: `the November 2 reference manuscript` (SP) lines 3060-3073.
Under the hypotheses `E0.WPRHyp` of the weighted product rule, the pointwise derivative
`∂_r(w‖f‖²) = ∂_r w ‖f‖² + 2 w Re(conj f · f')` (`HasDerivAt.norm_sq`, `Complex.inner`) is
integrated term by term: `∂_r(w‖f‖²)` is integrable (`wprInteg`), `∂_r w ‖f‖²` is dominated by
`C w ‖f‖²`, hence `w Re(conj f · f')` is integrable as the difference.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

open UnforcedLeray.Short.IIIa

/-- **`WPRSplit`**: `∫ ∂_r(w‖f‖²) = ∫ ∂_r w ‖f‖² + 2 ∫ w Re(conj f · f')`. -/
theorem wprSplit : WPRSplit := by
  intro μ w f f' r hH
  obtain ⟨hDint, hI0, -⟩ := wprInteg μ w f f' r hH
  obtain ⟨hw, hf, ⟨C, δ, -, hδ, hball⟩, hd, -, -, -⟩ := hH
  have hrb : r ∈ ball r δ := mem_ball_self hδ
  have hfr : AEStronglyMeasurable (f r) μ := hf.self_of_nhds
  have hpt : ∀ x, deriv (fun q => w q x * ‖f q x‖ ^ 2) r =
      deriv (fun q => w q x) r * ‖f r x‖ ^ 2 +
        2 * (w r x * ((starRingEnd ℂ) (f r x) * f' x).re) := by
    intro x
    have h : HasDerivAt (fun q => w q x * ‖f q x‖ ^ 2)
        (deriv (fun q => w q x) r * ‖f r x‖ ^ 2 + w r x * (2 * inner ℝ (f r x) (f' x))) r :=
      ((hball x r hrb).1.hasDerivAt).mul (hd x).norm_sq
    rw [h.deriv, Complex.inner, mul_comm (f' x)]
    ring
  have hWm : AEStronglyMeasurable (fun x => deriv (fun q => w q x) r) μ :=
    E0.wpr_aesm_of_hasDerivAt (fun q x => w q x) r
      (Eventually.of_forall fun q => (hw q).aestronglyMeasurable) _
      (fun x => (hball x r hrb).1.hasDerivAt)
  have hA : Integrable (fun x => deriv (fun q => w q x) r * ‖f r x‖ ^ 2) μ := by
    refine Integrable.mono' (hI0.const_mul C) (hWm.mul (hfr.norm.pow 2))
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖f r x‖)]
    calc |deriv (fun q => w q x) r| * ‖f r x‖ ^ 2 ≤ C * w r x * ‖f r x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hball x r hrb).2.2.2 (sq_nonneg _)
      _ = C * (w r x * ‖f r x‖ ^ 2) := by ring
  have hB : Integrable (fun x => 2 * (w r x * ((starRingEnd ℂ) (f r x) * f' x).re)) μ := by
    refine (hDint.sub hA).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hpt x]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hA hB, integral_const_mul]

end UnforcedLeray.Short.IIIa.AdjE1
