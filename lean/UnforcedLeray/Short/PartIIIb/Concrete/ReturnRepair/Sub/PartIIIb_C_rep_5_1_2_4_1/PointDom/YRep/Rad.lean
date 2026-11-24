import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The radial integral of the outward primitive

Source `the November 2 reference manuscript` 4180-4186: across the radial gap,
`∫_r^∞ ρ ((ρ - ρ₀)² + h²)^{-2} dρ ≤ C (δ² + h²)^{-1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_rad_deriv {ρ₀ h : ℝ} {r : ℝ} (hr : ρ₀ < r) :
    ∀ x ∈ Ici r, HasDerivAt (fun ρ : ℝ => -(((ρ - ρ₀) ^ 2 + h ^ 2)⁻¹))
      (2 * (x - ρ₀) / (((x - ρ₀) ^ 2 + h ^ 2) ^ 2)) x := by
  intro x hx
  have hx' : ρ₀ < x := lt_of_lt_of_le hr hx
  have hpos : 0 < (x - ρ₀) ^ 2 + h ^ 2 := by nlinarith [sq_nonneg h, sq_pos_of_pos (sub_pos.2 hx')]
  have h1 : HasDerivAt (fun ρ : ℝ => (ρ - ρ₀) ^ 2 + h ^ 2) (2 * (x - ρ₀)) x := by
    have := ((hasDerivAt_id x).sub_const ρ₀).pow 2
    simpa using this.add_const (h ^ 2)
  exact ((h1.inv hpos.ne').neg).congr_deriv (by ring)

lemma yr_rad_lint {ρ₀ δ r h C : ℝ} (hδ : 0 < δ) (hr : ρ₀ + δ ≤ r) (hC : 0 ≤ C) (f : ℝ → ℝ)
    (hf : ∀ ρ ∈ Ioi r, f ρ ≤ C * (ρ - ρ₀) / (((ρ - ρ₀) ^ 2 + h ^ 2) ^ 2)) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal (f ρ) ≤ ENNReal.ofReal (C / 2 / (δ ^ 2 + h ^ 2)) := by
  have hρr : ρ₀ < r := by linarith
  set g : ℝ → ℝ := fun ρ => C / 2 * (2 * (ρ - ρ₀) / (((ρ - ρ₀) ^ 2 + h ^ 2) ^ 2)) with hg
  have hgpos : ∀ x ∈ Ioi r, 0 ≤ g x := by
    intro x hx
    have : ρ₀ < x := lt_trans hρr hx
    simp only [hg]
    have h0 : 0 < x - ρ₀ := sub_pos.2 this
    exact mul_nonneg (by linarith) (div_nonneg (by linarith) (by positivity))
  have hder : ∀ x ∈ Ici r, HasDerivAt (fun ρ : ℝ => C / 2 * (-(((ρ - ρ₀) ^ 2 + h ^ 2)⁻¹))) (g x) x :=
    fun x hx => (yr_rad_deriv hρr x hx).const_mul (C / 2)
  have hlim : Tendsto (fun ρ : ℝ => C / 2 * (-(((ρ - ρ₀) ^ 2 + h ^ 2)⁻¹))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => ρ - ρ₀) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    have h2 : Tendsto (fun ρ : ℝ => (ρ - ρ₀) ^ 2) atTop atTop := (tendsto_pow_atTop two_ne_zero).comp h1
    have h3 : Tendsto (fun ρ : ℝ => (ρ - ρ₀) ^ 2 + h ^ 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ h2
    have h4 := (tendsto_inv_atTop_zero.comp h3).neg.const_mul (C / 2)
    simpa using h4
  have hint : IntegrableOn g (Ioi r) :=
    integrableOn_Ioi_deriv_of_nonneg' hder hgpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hder hgpos hlim
  have hfg : ∀ ρ ∈ Ioi r, f ρ ≤ g ρ := by
    intro ρ hρ
    refine (hf ρ hρ).trans (le_of_eq ?_)
    simp only [hg]; ring
  calc ∫⁻ ρ in Ioi r, ENNReal.ofReal (f ρ) ≤ ∫⁻ ρ in Ioi r, ENNReal.ofReal (g ρ) :=
        setLIntegral_mono' measurableSet_Ioi (fun ρ hρ => ENNReal.ofReal_le_ofReal (hfg ρ hρ))
    _ = ENNReal.ofReal (∫ ρ in Ioi r, g ρ) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hgpos))).symm
    _ ≤ ENNReal.ofReal (C / 2 / (δ ^ 2 + h ^ 2)) := by
        rw [hval]
        refine ENNReal.ofReal_le_ofReal ?_
        have hp : 0 < (r - ρ₀) ^ 2 + h ^ 2 := by
          nlinarith [sq_nonneg h, sq_pos_of_pos (sub_pos.2 hρr)]
        have hd : δ ^ 2 + h ^ 2 ≤ (r - ρ₀) ^ 2 + h ^ 2 := by nlinarith
        simp only [mul_neg, zero_sub, neg_neg]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hd) (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete

end
