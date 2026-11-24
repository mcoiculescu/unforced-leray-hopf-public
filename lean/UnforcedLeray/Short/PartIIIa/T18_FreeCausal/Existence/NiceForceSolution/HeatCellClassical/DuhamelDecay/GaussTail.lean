import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_4

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4/1`: one-dimensional Gaussian tail

Target: `duhDecGaussTail : DuhDecGaussTail` (`Sub/PartIIIa_T18_2_4_1_4.lean`, leaf 1 of the
Duhamel decay; SP 3427-3440 of `the November 2 reference manuscript`).

For `θ > 0`, `A ≥ 0`, the set `{t | A ≤ |t|}` carries
`G_θ(t) = (4πθ)^{-1/2} e^{-t²/(4θ)} ≤ e^{-A²/(8θ)} (4πθ)^{-1/2} e^{-t²/(8θ)}`, since
`t² ≥ A²` there. Enlarging the domain to `ℝ` and using `∫ (4πθ)^{-1/2} e^{-t²/(8θ)} = √2 ≤ 2`
(Mathlib `integral_gaussian`) gives the bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem duhDecGaussTail : UnforcedLeray.Short.IIIa.DuhDecGaussTail := by
  intro θ A hθ hA
  have hb : (0 : ℝ) < 1 / (8 * θ) := by positivity
  have hK : (0 : ℝ) ≤ (Real.sqrt (4 * Real.pi * θ))⁻¹ := by positivity
  have hfun : ∀ t : ℝ, UnforcedLeray.B0191.heatKernel 1 θ t
      = (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-t ^ 2 / (4 * θ)) := by
    intro t
    simp only [UnforcedLeray.B0191.heatKernel, mul_one]
  have hG_int : MeasureTheory.Integrable
      (fun t : ℝ => (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  have hs : 0 < Real.sqrt (4 * Real.pi * θ) := Real.sqrt_pos.mpr (by positivity)
  have hG_val : ∫ t : ℝ, (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2)
      = Real.sqrt 2 := by
    rw [integral_const_mul, integral_gaussian]
    have h1 : Real.pi / (1 / (8 * θ)) = 2 * (4 * Real.pi * θ) := by
      rw [div_div_eq_mul_div]
      ring
    rw [h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
      mul_comm (Real.sqrt (4 * Real.pi * θ))⁻¹ (Real.sqrt 2), mul_assoc,
      inv_mul_cancel₀ hs.ne', mul_one]
  have hsq : ∀ t : ℝ, A ≤ |t| → A ^ 2 ≤ t ^ 2 := by
    intro t ht
    nlinarith [abs_nonneg t, sq_abs t]
  have hpt : ∀ t ∈ {t : ℝ | A ≤ |t|},
      UnforcedLeray.B0191.heatKernel 1 θ t ≤
        Real.exp (-A ^ 2 / (8 * θ)) *
          ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2)) := by
    intro t ht
    have ht' : A ≤ |t| := ht
    have h2 : A ^ 2 ≤ t ^ 2 := hsq t ht'
    have key : -A ^ 2 / (8 * θ) + -(1 / (8 * θ)) * t ^ 2 - (-t ^ 2 / (4 * θ))
        = (t ^ 2 - A ^ 2) / (8 * θ) := by
      ring
    have hnn : 0 ≤ (t ^ 2 - A ^ 2) / (8 * θ) := div_nonneg (by linarith) (by positivity)
    have hexp : Real.exp (-t ^ 2 / (4 * θ)) ≤
        Real.exp (-A ^ 2 / (8 * θ)) * Real.exp (-(1 / (8 * θ)) * t ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    rw [hfun t]
    calc (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-t ^ 2 / (4 * θ))
        ≤ (Real.sqrt (4 * Real.pi * θ))⁻¹ *
            (Real.exp (-A ^ 2 / (8 * θ)) * Real.exp (-(1 / (8 * θ)) * t ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp hK
      _ = Real.exp (-A ^ 2 / (8 * θ)) *
            ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2)) := by ring
  have hb4 : (0 : ℝ) < 1 / (4 * θ) := by positivity
  have hint_hk : MeasureTheory.Integrable
      (fun t : ℝ => UnforcedLeray.B0191.heatKernel 1 θ t) := by
    have h4 : (fun t : ℝ => UnforcedLeray.B0191.heatKernel 1 θ t)
        = fun t : ℝ => (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (4 * θ)) * t ^ 2) := by
      funext t
      rw [hfun t, show -t ^ 2 / (4 * θ) = -(1 / (4 * θ)) * t ^ 2 by ring]
    rw [h4]
    exact (integrable_exp_neg_mul_sq hb4).const_mul _
  have hmeas : MeasurableSet {t : ℝ | A ≤ |t|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hint_set_le : ∫ t in {t : ℝ | A ≤ |t|}, UnforcedLeray.B0191.heatKernel 1 θ t
      ≤ ∫ t in {t : ℝ | A ≤ |t|}, Real.exp (-A ^ 2 / (8 * θ)) *
          ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2)) := by
    apply setIntegral_mono_on
      (hint_hk.integrableOn)
      ((hG_int.const_mul _).integrableOn) hmeas hpt
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun t : ℝ => (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2)) :=
    Filter.Eventually.of_forall fun t => by positivity
  have hle_full : ∫ t in {t : ℝ | A ≤ |t|}, Real.exp (-A ^ 2 / (8 * θ)) *
          ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-(1 / (8 * θ)) * t ^ 2))
      ≤ Real.exp (-A ^ 2 / (8 * θ)) * Real.sqrt 2 := by
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    rw [← hG_val]
    exact setIntegral_le_integral hG_int hnonneg
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hfin := mul_le_mul_of_nonneg_left hs2 (Real.exp_nonneg (-A ^ 2 / (8 * θ)))
  exact hint_set_le.trans (hle_full.trans (by linarith))

end UnforcedLeray.Short.IIIa
