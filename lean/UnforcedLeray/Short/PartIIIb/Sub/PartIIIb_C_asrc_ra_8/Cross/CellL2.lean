import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs
import UnforcedLeray.Lib.Cylinder.CellModes
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : normalized cell norm of a field with Gaussian `η`-decay

Source `the November 2 reference manuscript`
5029-5031 (cell norms), with the normalized cell measure `Cyl.avgμ c = c⁻¹ dq dη` on
`[-c/2, c/2) × ℝ`.  If `|f(q, η)| ≤ D e^{-η²/34}` then `|f|² ≤ D² e^{-η²/17}` pointwise, the cell
integral of a function of `η` alone is `c` times its line integral (`lintegral_cell_snd_le`), and
`∫ e^{-η²/17} dη = √(17π)` (`integral_gaussian`); `|toMer v|² ≤ 2|v|²_∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rc_toMer_norm_sq_le (v : ℝ × ℝ) : ‖toMer v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  unfold toMer
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Fin.sum_univ_two]
  have e0 : ‖(!₂[v.1, v.2] : UnforcedLeray.Axi.Merid) 0‖ = ‖v.1‖ := rfl
  have e1 : ‖(!₂[v.1, v.2] : UnforcedLeray.Axi.Merid) 1‖ = ‖v.2‖ := rfl
  rw [e0, e1]
  have a1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have a2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  nlinarith [norm_nonneg v.1, norm_nonneg v.2]

theorem rcCellGaussL2 : RcCellGaussL2 := by
  refine ⟨Real.sqrt (2 * Real.sqrt (Real.pi / (1 / 17))), Real.sqrt_nonneg _, ?_⟩
  intro c D f hc hD hf
  set I := Real.sqrt (Real.pi / (1 / 17)) with hI
  have hI0 : 0 ≤ I := Real.sqrt_nonneg _
  set G : ℝ → ENNReal := fun η => ENNReal.ofReal (2 * D ^ 2 * Real.exp (-(1 / 17) * η ^ 2))
    with hGdef
  have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (‖toMer (f x)‖ ^ 2) ≤ G x.2 := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    have h1 := rc_toMer_norm_sq_le (f x)
    have h2 : ‖f x‖ ^ 2 ≤ (D * Real.exp (-(x.2 ^ 2) / 34)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
    have h3 : (D * Real.exp (-(x.2 ^ 2) / 34)) ^ 2 = D ^ 2 * Real.exp (-(1 / 17) * x.2 ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [h3] at h2
    linarith
  have hint : Integrable (fun η : ℝ => 2 * D ^ 2 * Real.exp (-(1 / 17) * η ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 17)).const_mul _
  have hline : ∫⁻ η, G η = ENNReal.ofReal (2 * D ^ 2 * I) := by
    rw [hGdef]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun η => by positivity)]
    rw [integral_const_mul, integral_gaussian]
  calc ∫⁻ x, ENNReal.ofReal (‖toMer (f x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c)
      ≤ ∫⁻ x, G x.2 ∂(UnforcedLeray.Cyl.avgμ c) := lintegral_mono hpt
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, G z.2 :=
        UnforcedLeray.Cyl.lintegral_avgμ _
    _ ≤ ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ∫⁻ η, G η) := by
        gcongr
        exact UnforcedLeray.Cyl.lintegral_cell_snd_le hc G
    _ = ∫⁻ η, G η := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (2 * D ^ 2 * I) := hline
    _ = ENNReal.ofReal ((Real.sqrt (2 * I) * D) ^ 2) := by
        congr 1
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
