import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- Scaling identity: `θ · G_θ(√θ w) = G_1(w)` on `ℝ²` (source 1650-1656). -/
theorem t0g_gauss_scale {θ : ℝ} (hθ : 0 < θ) (w : UnforcedLeray.Gaussian.Euc 2) :
    θ * UnforcedLeray.Gaussian.gaussKernel 2 θ (Real.sqrt θ • w) =
      UnforcedLeray.Gaussian.gaussKernel 2 1 w := by
  have hn : ‖Real.sqrt θ • w‖ ^ 2 = θ * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hθ.le]
  have e : ∀ t : ℝ, (4 * Real.pi * t) ^ (-((2 : ℕ) : ℝ) / 2) = (4 * Real.pi * t)⁻¹ := by
    intro t
    rw [show -((2 : ℕ) : ℝ) / 2 = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  simp only [UnforcedLeray.Gaussian.gaussKernel, e]
  rw [hn]
  have hexp : -(θ * ‖w‖ ^ 2) / (4 * θ) = -‖w‖ ^ 2 / (4 * 1) := by
    field_simp
  rw [hexp]
  field_simp

theorem t0gHeatSub_proof : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gHeatSub := by
  intro θ hθ u x
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  simp only [smul_eq_mul]
  have hfac : |((Real.sqrt θ) ^ Module.finrank ℝ (UnforcedLeray.Gaussian.Euc 2))⁻¹| = θ⁻¹ := by
    rw [UnforcedLeray.Gaussian.finrank_euc, Real.sq_sqrt hθ.le, abs_of_pos (inv_pos.2 hθ)]
  have hsub : ∫ w : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ (Real.sqrt θ • w) *
        u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • w)) =
      θ⁻¹ • ∫ y : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ y * u (x - UnforcedLeray.B0224.planeι y) := by
    have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (UnforcedLeray.Gaussian.Euc 2))
      (fun y : UnforcedLeray.Gaussian.Euc 2 =>
        UnforcedLeray.Gaussian.gaussKernel 2 θ y * u (x - UnforcedLeray.B0224.planeι y))
      (Real.sqrt θ)
    rw [hfac] at h
    exact h
  have hI : ∫ y : UnforcedLeray.Gaussian.Euc 2,
      UnforcedLeray.Gaussian.gaussKernel 2 θ y * u (x - UnforcedLeray.B0224.planeι y) =
      θ * ∫ w : UnforcedLeray.Gaussian.Euc 2,
        UnforcedLeray.Gaussian.gaussKernel 2 θ (Real.sqrt θ • w) *
          u (x - UnforcedLeray.B0224.planeι (Real.sqrt θ • w)) := by
    rw [hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
  rw [hI, ← integral_const_mul]
  congr 1
  funext w
  rw [← mul_assoc, t0g_gauss_scale hθ w]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
