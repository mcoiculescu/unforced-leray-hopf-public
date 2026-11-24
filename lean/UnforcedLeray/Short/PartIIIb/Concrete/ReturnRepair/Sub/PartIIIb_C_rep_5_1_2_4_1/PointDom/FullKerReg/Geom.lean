import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.HDeriv4

/-!
# Geometry of the receiver region
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem varrho_le_norm (y : Space) : ϱ y ≤ ‖y‖ := by
  have h : ϱ y ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_sq_eq_ϱ_sq_add]; nlinarith [sq_nonneg (y 2)]
  exact (abs_le_of_sq_le_sq' h (norm_nonneg _)).2

theorem varrho_triangle (a b : Space) : ϱ a ≤ ϱ (a - b) + ϱ b := by
  have hp := ϱ_sq (a - b)
  have hb := ϱ_sq b
  have hp0 := ϱ_nonneg (a - b)
  have hb0 := ϱ_nonneg b
  have hcs : ((a - b) 0 * b 0 + (a - b) 1 * b 1) ≤ ϱ (a - b) * ϱ b := by
    have h2 : ((a - b) 0 * b 0 + (a - b) 1 * b 1) ^ 2 ≤ (ϱ (a - b) * ϱ b) ^ 2 := by
      rw [mul_pow, hp, hb]; nlinarith [sq_nonneg ((a - b) 0 * b 1 - (a - b) 1 * b 0)]
    exact (abs_le_of_sq_le_sq' h2 (mul_nonneg hp0 hb0)).2
  have h : ϱ a ^ 2 ≤ (ϱ (a - b) + ϱ b) ^ 2 := by
    rw [ϱ_sq a]
    have e0 : a 0 = (a - b) 0 + b 0 := by simp
    have e1 : a 1 = (a - b) 1 + b 1 := by simp
    rw [e0, e1]
    nlinarith
  exact (abs_le_of_sq_le_sq' h (add_nonneg hp0 hb0)).2

/-- `‖y - λ z‖ ≥ r₁ - ρ₀` for `ϱ y > r₁`, `ϱ z ≤ ρ₀`, `λ ∈ (0,1]`. -/
theorem norm_sub_lam_ge {y z : Space} {l r₁ ρ₀ : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hz : ϱ z ≤ ρ₀)
    (hy : r₁ < ϱ y) : r₁ - ρ₀ ≤ ‖y - l • z‖ := by
  have h1 := varrho_triangle y (l • z)
  rw [ϱ_smul, abs_of_pos hl0] at h1
  have h2 := varrho_le_norm (y - l • z)
  have h3 : l * ϱ z ≤ ρ₀ := by
    have := ϱ_nonneg z
    nlinarith
  linarith

theorem lam_norm_le {y z : Space} {l Y : ℝ} (hl0 : 0 < l) (hy : ‖y‖ < Y) :
    l * ‖z‖ ≤ ‖y - l • z‖ + Y := by
  have e : l • z = y - (y - l • z) := by abel
  have h1 : ‖l • z‖ ≤ ‖y‖ + ‖y - l • z‖ := by
    calc ‖l • z‖ = ‖y - (y - l • z)‖ := by rw [← e]
      _ ≤ ‖y‖ + ‖y - l • z‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0] at h1
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
