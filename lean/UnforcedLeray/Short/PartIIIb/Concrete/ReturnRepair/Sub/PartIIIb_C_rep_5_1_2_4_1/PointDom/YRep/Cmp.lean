import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.Geom
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary comparisons for `pdYRep`

Source `the November 2 reference manuscript` 3611-3621, 4171, 4180-4186.
Comparison of `srcWeight` at nearby phases, and the lower bound `‖x - λz‖ ≥ (1+λ‖z‖)/κ` across
the radial gap.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  nlinarith

lemma yr_shift_factor (d : ℝ) (hd : |d| ≤ 1) :
    Real.exp (-(d / 2)) ≤ 2 ∧ 1 / 2 ≤ Real.exp (-(d / 2)) := by
  have hd' := abs_le.1 hd
  have h2 := yr_exp_half_lt_two
  constructor
  · calc Real.exp (-(d / 2)) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 2 := h2.le
  · have : Real.exp (-(1 / 2)) ≤ Real.exp (-(d / 2)) := Real.exp_le_exp.2 (by linarith)
    refine le_trans ?_ this
    rw [Real.exp_neg]
    have h3 : 0 < Real.exp (1 / 2) := Real.exp_pos _
    rw [le_inv_comm₀ (by norm_num) h3]
    linarith

lemma yr_pdLam_shift (h h' : ℝ) : pdLam h' = pdLam h * Real.exp (-((h' - h) / 2)) := by
  unfold pdLam
  rw [← Real.exp_add]; congr 1; ring

lemma yr_srcWeight_cmp (μ : ℝ) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (h h' : ℝ) (z : Space)
    (hd : |h' - h| ≤ 1) : srcWeight μ h' z ≤ 512 * srcWeight μ h z := by
  obtain ⟨hq2, hq1⟩ := yr_shift_factor (h' - h) hd
  set q := Real.exp (-((h' - h) / 2)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hl0 : 0 < pdLam h := Real.exp_pos _
  have hl' : pdLam h' = pdLam h * q := yr_pdLam_shift h h'
  set l := pdLam h with hl
  have ha0 : 0 ≤ 2 * μ + 3 := by linarith
  have ha5 : 2 * μ + 3 ≤ 5 := by linarith
  have hqa : q ^ (2 * μ + 3) ≤ 32 := by
    calc q ^ (2 * μ + 3) ≤ (2 : ℝ) ^ (2 * μ + 3) := Real.rpow_le_rpow hq0.le hq2 ha0
      _ ≤ (2 : ℝ) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha5
      _ = 32 := by
        rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hpow : pdLam h' ^ (2 * μ + 3) ≤ 32 * l ^ (2 * μ + 3) := by
    rw [hl', Real.mul_rpow hl0.le hq0.le]
    have := Real.rpow_nonneg hl0.le (2 * μ + 3)
    nlinarith
  have hz := norm_nonneg z
  have hA : (1 + l * ‖z‖) / 2 ≤ 1 + pdLam h' * ‖z‖ := by
    rw [hl']; nlinarith [mul_nonneg hl0.le hz, mul_nonneg hl0.le (mul_nonneg hz hq0.le)]
  have hA0 : 0 < 1 + l * ‖z‖ := by positivity
  have hT1 : ((1 + pdLam h' * ‖z‖) ^ 4)⁻¹ ≤ 16 * ((1 + l * ‖z‖) ^ 4)⁻¹ := by
    have h4 : ((1 + l * ‖z‖) / 2) ^ 4 ≤ (1 + pdLam h' * ‖z‖) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hA 4
    have h5 : ((1 + l * ‖z‖) / 2) ^ 4 = (1 + l * ‖z‖) ^ 4 / 16 := by ring
    rw [h5] at h4
    calc ((1 + pdLam h' * ‖z‖) ^ 4)⁻¹ ≤ ((1 + l * ‖z‖) ^ 4 / 16)⁻¹ :=
          inv_anti₀ (by positivity) h4
      _ = 16 * ((1 + l * ‖z‖) ^ 4)⁻¹ := by rw [inv_div]; ring
  have hB : (1 + (l * z 2) ^ 2) / 4 ≤ 1 + (pdLam h' * z 2) ^ 2 := by
    rw [hl']
    have : (l * q * z 2) ^ 2 = q ^ 2 * (l * z 2) ^ 2 := by ring
    have hq4 : 1 / 4 ≤ q ^ 2 := by nlinarith
    nlinarith [sq_nonneg (l * z 2)]
  have hT2 : (1 + (pdLam h' * z 2) ^ 2)⁻¹ ≤ 4 * (1 + (l * z 2) ^ 2)⁻¹ := by
    calc (1 + (pdLam h' * z 2) ^ 2)⁻¹ ≤ ((1 + (l * z 2) ^ 2) / 4)⁻¹ :=
          inv_anti₀ (by positivity) hB
      _ = 4 * (1 + (l * z 2) ^ 2)⁻¹ := by rw [inv_div]; ring
  have hp1 : 0 ≤ ((1 + l * ‖z‖) ^ 4)⁻¹ := by positivity
  have hp2 : 0 ≤ (1 + (l * z 2) ^ 2)⁻¹ := by positivity
  have hlp : 0 ≤ l ^ (2 * μ + 3) := Real.rpow_nonneg hl0.le _
  have hpp : 0 ≤ pdLam h' ^ (2 * μ + 3) := Real.rpow_nonneg (Real.exp_pos _).le _
  unfold srcWeight
  show pdLam h' ^ (2 * μ + 3) * _ ≤ 512 * (l ^ (2 * μ + 3) * _)
  have hsum : ((1 + pdLam h' * ‖z‖) ^ 4)⁻¹ + (1 + (pdLam h' * z 2) ^ 2)⁻¹ ≤
      16 * (((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹) := by linarith
  calc pdLam h' ^ (2 * μ + 3) * (((1 + pdLam h' * ‖z‖) ^ 4)⁻¹ + (1 + (pdLam h' * z 2) ^ 2)⁻¹)
      ≤ (32 * l ^ (2 * μ + 3)) * (16 * (((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹)) :=
        mul_le_mul hpow hsum (by positivity) (by positivity)
    _ = 512 * (l ^ (2 * μ + 3) * (((1 + l * ‖z‖) ^ 4)⁻¹ + (1 + (l * z 2) ^ 2)⁻¹)) := by ring

lemma yr_srcWeight_nonneg (μ h : ℝ) (z : Space) : 0 ≤ srcWeight μ h z := by
  unfold srcWeight
  have := Real.rpow_nonneg (Real.exp_pos (-(h / 2))).le (2 * μ + 3)
  have h1 : 0 ≤ ((1 + pdLam h * ‖z‖) ^ 4)⁻¹ := by
    have : 0 ≤ pdLam h := (Real.exp_pos _).le
    positivity
  have h2 : 0 ≤ (1 + (pdLam h * z 2) ^ 2)⁻¹ := by positivity
  exact mul_nonneg (by simpa [pdLam] using this) (add_nonneg h1 h2)

/-- Lower bound for the translated kernel across the radial gap:
`1 + λ‖z‖ ≤ κ ‖x - λ z‖`, `κ = 1/δ + 1 + Y/δ`, `δ = r₁ - ρ₀`. -/
lemma yr_gap_lower {x z : Space} {l r₁ ρ₀ Y : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hz : ϱ z ≤ ρ₀)
    (hρ : ρ₀ < r₁) (hx : r₁ < ϱ x) (hxY : ‖x‖ < Y) :
    1 + l * ‖z‖ ≤ (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) * ‖x - l • z‖ := by
  have hδ : 0 < r₁ - ρ₀ := by linarith
  have h1 := norm_sub_lam_ge hl0 hl1 hz hx
  have h2 := lam_norm_le (z := z) hl0 hxY
  have hn : 0 ≤ ‖x - l • z‖ := norm_nonneg _
  have h3 : 1 ≤ ‖x - l • z‖ / (r₁ - ρ₀) := by rw [le_div_iff₀ hδ]; linarith
  have h4 : Y ≤ Y * (‖x - l • z‖ / (r₁ - ρ₀)) := by
    have hY : 0 ≤ Y := by linarith [norm_nonneg x]
    nlinarith
  have : (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) * ‖x - l • z‖ =
      ‖x - l • z‖ / (r₁ - ρ₀) + ‖x - l • z‖ + Y * (‖x - l • z‖ / (r₁ - ρ₀)) := by
    field_simp
  rw [this]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
