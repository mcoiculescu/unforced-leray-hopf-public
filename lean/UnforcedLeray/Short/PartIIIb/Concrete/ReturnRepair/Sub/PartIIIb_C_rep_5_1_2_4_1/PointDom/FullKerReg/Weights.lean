import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.HPart2

/-!
# Comparison of the geometric decay with the source weight `srcWeight`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem weightX {y z : Space} {l r₁ ρ₀ Y : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hz : ϱ z ≤ ρ₀)
    (hρr : ρ₀ < r₁) (hy : r₁ < ϱ y) (hyY : ‖y‖ < Y) :
    (‖y - l • z‖ ^ 4)⁻¹ ≤ (1 / (r₁ - ρ₀) + 1 + Y / (r₁ - ρ₀)) ^ 4 * ((1 + l * ‖z‖) ^ 4)⁻¹ := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hxδ : δ ≤ ‖y - l • z‖ := norm_sub_lam_ge hl0 hl1 hz hy
  have hlz := lam_norm_le (z := z) hl0 hyY
  have hY0 : 0 ≤ Y := by have := norm_nonneg y; linarith
  set x := ‖y - l • z‖ with hx
  have hxp : 0 < x := lt_of_lt_of_le hδ0 hxδ
  set κ := 1 / δ + 1 + Y / δ with hκ
  have hκ0 : 0 < κ := by positivity
  have h1 : 1 + l * ‖z‖ ≤ κ * x := by
    have e1 : 1 ≤ x / δ := by rw [le_div_iff₀ hδ0]; linarith
    have e2 : Y ≤ Y / δ * x := by
      calc Y = Y / δ * δ := by field_simp
        _ ≤ Y / δ * x := mul_le_mul_of_nonneg_left hxδ (by positivity)
    have : κ * x = x / δ + x + Y / δ * x := by rw [hκ]; ring
    rw [this]; linarith
  have hp : 0 < (1 + l * ‖z‖) ^ 4 := by positivity
  have h2 : (1 + l * ‖z‖) ^ 4 ≤ κ ^ 4 * x ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 4
  have h3 : (x ^ 4)⁻¹ ≤ κ ^ 4 * ((1 + l * ‖z‖) ^ 4)⁻¹ := by
    have := inv_anti₀ hp h2
    calc (x ^ 4)⁻¹ = κ ^ 4 * (κ ^ 4 * x ^ 4)⁻¹ := by field_simp
      _ ≤ κ ^ 4 * ((1 + l * ‖z‖) ^ 4)⁻¹ := mul_le_mul_of_nonneg_left this (by positivity)
  exact h3

theorem weightS {y z : Space} {l r₁ ρ₀ Y : ℝ} (hρr : ρ₀ < r₁) (hy : r₁ < ϱ y) (hyY : ‖y‖ < Y) :
    1 / (2 * ((ϱ y - ρ₀) ^ 2 + (y 2 - l * z 2) ^ 2)) ≤
      (((1 + 2 * Y ^ 2) / (r₁ - ρ₀) ^ 2 + 2) / 2) * (1 + (l * z 2) ^ 2)⁻¹ := by
  set δ := r₁ - ρ₀ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have ha : δ ≤ ϱ y - ρ₀ := by rw [hδ]; linarith
  set b := y 2 - l * z 2 with hb
  have hy2 : y 2 ^ 2 ≤ Y ^ 2 := by
    have h1 : |y 2| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 2
    have h2 : |y 2| ≤ Y := h1.trans hyY.le
    exact sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  have hlz : (l * z 2) ^ 2 ≤ 2 * b ^ 2 + 2 * Y ^ 2 := by
    have : l * z 2 = y 2 - b := by rw [hb]; ring
    rw [this]; nlinarith [sq_nonneg (y 2 + b)]
  set c₃ := (1 + 2 * Y ^ 2) / δ ^ 2 + 2 with hc₃
  have hc3 : 0 < c₃ := by positivity
  have ha2 : δ ^ 2 ≤ (ϱ y - ρ₀) ^ 2 := pow_le_pow_left₀ hδ0.le ha 2
  have hkey : 1 + (l * z 2) ^ 2 ≤ c₃ * ((ϱ y - ρ₀) ^ 2 + b ^ 2) := by
    have e1 : 1 + 2 * Y ^ 2 ≤ (1 + 2 * Y ^ 2) / δ ^ 2 * (ϱ y - ρ₀) ^ 2 := by
      calc 1 + 2 * Y ^ 2 = (1 + 2 * Y ^ 2) / δ ^ 2 * δ ^ 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left ha2 (by positivity)
    nlinarith [sq_nonneg b, sq_nonneg (ϱ y - ρ₀), mul_nonneg (by positivity : (0:ℝ) ≤ 2) (sq_nonneg (ϱ y - ρ₀))]
  have hs : 0 < (ϱ y - ρ₀) ^ 2 + b ^ 2 := by nlinarith [pow_pos hδ0 2, sq_nonneg b]
  rw [div_le_iff₀ (by linarith [hs])]
  have hinv : (1 + (l * z 2) ^ 2)⁻¹ * (1 + (l * z 2) ^ 2) = 1 := inv_mul_cancel₀ (by positivity)
  have : c₃ / 2 * (1 + (l * z 2) ^ 2)⁻¹ * (2 * ((ϱ y - ρ₀) ^ 2 + b ^ 2)) =
      (1 + (l * z 2) ^ 2)⁻¹ * (c₃ * ((ϱ y - ρ₀) ^ 2 + b ^ 2)) := by ring
  rw [this]
  calc (1 : ℝ) = (1 + (l * z 2) ^ 2)⁻¹ * (1 + (l * z 2) ^ 2) := hinv.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete

end
