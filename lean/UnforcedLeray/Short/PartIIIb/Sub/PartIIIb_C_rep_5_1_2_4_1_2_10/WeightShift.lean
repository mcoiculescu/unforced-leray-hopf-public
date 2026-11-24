import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# Shift of the weight `srcWeight` under a time translation

Source `the November 2 reference manuscript` 3631-3646 (dilated source).
With `l = pdLam h > 0` and `a = exp (s/2) ≥ 1` one has `pdLam (h - s) = a * l`, and the
weight is `l^(2μ+3)` times a bracket that is decreasing in `l`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem srcWeight_shift (μ : ℝ) (hμ : -(1 / 4) < μ) (h s : ℝ) (hs : 0 ≤ s) (z : Space) :
    srcWeight μ (h - s) z ≤ Real.exp ((2 * μ + 3) * (s / 2)) * srcWeight μ h z := by
  have hshift : pdLam (h - s) = Real.exp (s / 2) * pdLam h := by
    unfold pdLam
    rw [← Real.exp_add]
    congr 1
    ring
  have hL0 : 0 < pdLam h := Real.exp_pos _
  have ha0 : 0 < Real.exp (s / 2) := Real.exp_pos _
  have ha1 : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
  have hpow : Real.exp (s / 2) ^ (2 * μ + 3) = Real.exp ((2 * μ + 3) * (s / 2)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  unfold srcWeight
  rw [hshift, Real.mul_rpow ha0.le hL0.le, hpow]
  generalize pdLam h = L at hL0 ⊢
  generalize Real.exp (s / 2) = a at ha0 ha1 ⊢
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hLz : 0 ≤ L * ‖z‖ := mul_nonneg hL0.le hz
  have hp1 : 0 < 1 + L * ‖z‖ := by linarith
  have hk1 : (1 + L * ‖z‖) ^ 4 ≤ (1 + a * L * ‖z‖) ^ 4 := by
    apply pow_le_pow_left₀ (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hLz]
  have hA : ((1 + a * L * ‖z‖) ^ 4)⁻¹ ≤ ((1 + L * ‖z‖) ^ 4)⁻¹ :=
    inv_anti₀ (pow_pos hp1 4) hk1
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hk2 : (L * z 2) ^ 2 ≤ (a * L * z 2) ^ 2 := by
    have e : (a * L * z 2) ^ 2 = a ^ 2 * (L * z 2) ^ 2 := by ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg (L * z 2))]
  have hB : (1 + (a * L * z 2) ^ 2)⁻¹ ≤ (1 + (L * z 2) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hb : ((1 + a * L * ‖z‖) ^ 4)⁻¹ + (1 + (a * L * z 2) ^ 2)⁻¹ ≤
      ((1 + L * ‖z‖) ^ 4)⁻¹ + (1 + (L * z 2) ^ 2)⁻¹ := add_le_add hA hB
  have hE : 0 ≤ Real.exp ((2 * μ + 3) * (s / 2)) := (Real.exp_pos _).le
  have hc : 0 ≤ L ^ (2 * μ + 3) := Real.rpow_nonneg hL0.le _
  have key := mul_le_mul_of_nonneg_left hb (mul_nonneg hE hc)
  calc _ = (Real.exp ((2 * μ + 3) * (s / 2)) * L ^ (2 * μ + 3)) *
          (((1 + a * L * ‖z‖) ^ 4)⁻¹ + (1 + (a * L * z 2) ^ 2)⁻¹) := by ring
    _ ≤ _ := key
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
