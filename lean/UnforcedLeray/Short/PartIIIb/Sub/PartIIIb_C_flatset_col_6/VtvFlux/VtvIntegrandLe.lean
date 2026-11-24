import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Column

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/14`: pointwise bound of the tested integrand

Target (`VtvFluxLemmas.lean`): `VtvIntegrandLe`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

With `F = 0`, `forcedIntegrand` is the sum over `i` of `-(b_i ∂_sΦ_i) + (μ/s) b_i Φ_i - ν b_i ΔΦ_i`
plus `∑_j (-(v_i b_j + b_i v_j)) ∂_jΦ_i`, minus `∑_i f_i Φ_i`.  Each of these twelve summands is
bounded by a triangle inequality estimate; the `4Vδ` coefficient collects the four velocity-gradient
terms, and `‖μ/s‖ ≤ ‖μ‖/s₁` for `s ≥ s₁`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest flatIntegrand trainVel flatDt flatGrad flatLap fibK1)

theorem vtv_norm_real_cast (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem vtv_norm_sum12 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : ℂ) :
    ‖t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11‖ ≤
      ‖t0‖ + ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ + ‖t5‖ + ‖t6‖ + ‖t7‖ + ‖t8‖ + ‖t9‖ + ‖t10‖ + ‖t11‖ := by
  have h1 := norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10) t11
  have h2 := norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9) t10
  have h3 := norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) t9
  have h4 := norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7) t8
  have h5 := norm_add_le (t0 + t1 + t2 + t3 + t4 + t5 + t6) t7
  have h6 := norm_add_le (t0 + t1 + t2 + t3 + t4 + t5) t6
  have h7 := norm_add_le (t0 + t1 + t2 + t3 + t4) t5
  have h8 := norm_add_le (t0 + t1 + t2 + t3) t4
  have h9 := norm_add_le (t0 + t1 + t2) t3
  have h10 := norm_add_le (t0 + t1) t2
  have h11 := norm_add_le t0 t1
  linarith

/-- `‖-(z r)‖ ≤ δ ‖z‖` for a real factor `|r| ≤ δ`. -/
theorem vtv_bnd_neg_real (z : ℂ) (r δ : ℝ) (hr : |r| ≤ δ) :
    ‖-(z * (r : ℂ))‖ ≤ δ * ‖z‖ := by
  rw [norm_neg, norm_mul, vtv_norm_real_cast]
  have := mul_le_mul_of_nonneg_left hr (norm_nonneg z)
  linarith

/-- `‖x z r‖ ≤ c δ ‖z‖` for `‖x‖ ≤ c` and `|r| ≤ δ`. -/
theorem vtv_bnd_mul3 (x z : ℂ) (r c δ : ℝ) (hx : ‖x‖ ≤ c) (hr : |r| ≤ δ) :
    ‖x * z * (r : ℂ)‖ ≤ c * δ * ‖z‖ := by
  rw [norm_mul, norm_mul, vtv_norm_real_cast]
  have hc : 0 ≤ c := le_trans (norm_nonneg x) hx
  have h1 : ‖x‖ * ‖z‖ ≤ c * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
  have h2 : ‖x‖ * ‖z‖ * |r| ≤ c * ‖z‖ * δ :=
    mul_le_mul h1 hr (abs_nonneg r) (mul_nonneg hc (norm_nonneg z))
  linarith

/-- The velocity-gradient summand `-(v_a b + b v_c) g`. -/
theorem vtv_bnd_Q (a c : ℂ) (va vc g V δ : ℝ) (hV : 0 ≤ V) (hva : |va| ≤ V) (hvc : |vc| ≤ V)
    (hg : |g| ≤ δ) :
    ‖-((va : ℂ) * a + c * (vc : ℂ)) * (g : ℂ)‖ ≤ (V * ‖a‖ + ‖c‖ * V) * δ := by
  rw [norm_mul, norm_neg, vtv_norm_real_cast]
  have h1 : ‖(va : ℂ) * a + c * (vc : ℂ)‖ ≤ V * ‖a‖ + ‖c‖ * V := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, vtv_norm_real_cast, vtv_norm_real_cast]
    have ha := norm_nonneg a
    have hc := norm_nonneg c
    nlinarith [mul_le_mul_of_nonneg_right hva ha, mul_le_mul_of_nonneg_left hvc hc]
  have h2 := mul_le_mul h1 hg (abs_nonneg g)
    (add_nonneg (mul_nonneg hV (norm_nonneg a)) (mul_nonneg (norm_nonneg c) hV))
  linarith

/-- **Pointwise bound of the tested integrand** (source 3511-3514, the `δ`-size test estimate). -/
theorem vtvIntegrandLe : VtvIntegrandLe := by
  unfold VtvIntegrandLe
  intro ν μ vel f b Φ p s₁ δ V hs₁ hp hΦb hvel
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hΦb 0).1
  have hV : 0 ≤ V := le_trans (abs_nonneg _) (hvel 0)
  have hp1 : 0 < p.1 := lt_of_lt_of_le hs₁ hp
  have hm : ‖μ / (p.1 : ℂ)‖ ≤ ‖μ‖ / s₁ := by
    rw [norm_div, vtv_norm_real_cast, abs_of_pos hp1]
    gcongr
  have hm0 : 0 ≤ ‖μ‖ / s₁ := div_nonneg (norm_nonneg μ) hs₁.le
  have hνb : ‖-(ν : ℂ)‖ ≤ |ν| := by
    rw [norm_neg, vtv_norm_real_cast]
  have hE : forcedIntegrand ν μ vel f b Φ p =
      -(b p 0 * (flatDt Φ p.1 p.2 0 : ℂ))
      + (μ / (p.1 : ℂ)) * b p 0 * (Φ p.1 p.2 0 : ℂ)
      + (-(ν : ℂ)) * b p 0 * (flatLap Φ p.1 p.2 0 : ℂ)
      + -((vel p.1 p.2 0 : ℂ) * b p 0 + b p 0 * (vel p.1 p.2 0 : ℂ)) * (flatGrad Φ p.1 p.2 0 0 : ℂ)
      + -((vel p.1 p.2 0 : ℂ) * b p 1 + b p 0 * (vel p.1 p.2 1 : ℂ)) * (flatGrad Φ p.1 p.2 0 1 : ℂ)
      + -(b p 1 * (flatDt Φ p.1 p.2 1 : ℂ))
      + (μ / (p.1 : ℂ)) * b p 1 * (Φ p.1 p.2 1 : ℂ)
      + (-(ν : ℂ)) * b p 1 * (flatLap Φ p.1 p.2 1 : ℂ)
      + -((vel p.1 p.2 1 : ℂ) * b p 0 + b p 1 * (vel p.1 p.2 0 : ℂ)) * (flatGrad Φ p.1 p.2 1 0 : ℂ)
      + -((vel p.1 p.2 1 : ℂ) * b p 1 + b p 1 * (vel p.1 p.2 1 : ℂ)) * (flatGrad Φ p.1 p.2 1 1 : ℂ)
      + -(f p 0 * (Φ p.1 p.2 0 : ℂ))
      + -(f p 1 * (Φ p.1 p.2 1 : ℂ)) := by
    simp only [forcedIntegrand, flatIntegrand, Fin.sum_univ_two]
    ring
  rw [hE, Fin.sum_univ_two]
  refine le_trans (vtv_norm_sum12 _ _ _ _ _ _ _ _ _ _ _ _) ?_
  have e0 := vtv_bnd_neg_real (b p 0) _ δ (hΦb 0).2.1
  have e1 := vtv_bnd_mul3 (μ / (p.1 : ℂ)) (b p 0) _ (‖μ‖ / s₁) δ hm (hΦb 0).1
  have e2 := vtv_bnd_mul3 (-(ν : ℂ)) (b p 0) _ |ν| δ hνb (hΦb 0).2.2.1
  have e3 := vtv_bnd_Q (b p 0) (b p 0) _ _ _ V δ hV (hvel 0) (hvel 0) ((hΦb 0).2.2.2 0)
  have e4 := vtv_bnd_Q (b p 1) (b p 0) _ _ _ V δ hV (hvel 0) (hvel 1) ((hΦb 0).2.2.2 1)
  have e5 := vtv_bnd_neg_real (b p 1) _ δ (hΦb 1).2.1
  have e6 := vtv_bnd_mul3 (μ / (p.1 : ℂ)) (b p 1) _ (‖μ‖ / s₁) δ hm (hΦb 1).1
  have e7 := vtv_bnd_mul3 (-(ν : ℂ)) (b p 1) _ |ν| δ hνb (hΦb 1).2.2.1
  have e8 := vtv_bnd_Q (b p 0) (b p 1) _ _ _ V δ hV (hvel 1) (hvel 0) ((hΦb 1).2.2.2 0)
  have e9 := vtv_bnd_Q (b p 1) (b p 1) _ _ _ V δ hV (hvel 1) (hvel 1) ((hΦb 1).2.2.2 1)
  have e10 := vtv_bnd_neg_real (f p 0) _ δ (hΦb 0).1
  have e11 := vtv_bnd_neg_real (f p 1) _ δ (hΦb 1).1
  have n0 : 0 ≤ δ * (‖μ‖ / s₁) * ‖f p 0‖ := mul_nonneg (mul_nonneg hδ hm0) (norm_nonneg _)
  have n1 : 0 ≤ δ * (‖μ‖ / s₁) * ‖f p 1‖ := mul_nonneg (mul_nonneg hδ hm0) (norm_nonneg _)
  have n2 : 0 ≤ δ * |ν| * ‖f p 0‖ := mul_nonneg (mul_nonneg hδ (abs_nonneg ν)) (norm_nonneg _)
  have n3 : 0 ≤ δ * |ν| * ‖f p 1‖ := mul_nonneg (mul_nonneg hδ (abs_nonneg ν)) (norm_nonneg _)
  have n4 : 0 ≤ δ * V * ‖f p 0‖ := mul_nonneg (mul_nonneg hδ hV) (norm_nonneg _)
  have n5 : 0 ≤ δ * V * ‖f p 1‖ := mul_nonneg (mul_nonneg hδ hV) (norm_nonneg _)
  linarith [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, n0, n1, n2, n3, n4, n5]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
