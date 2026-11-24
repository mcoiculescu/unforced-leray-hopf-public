import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsTestConvBound

/-!
# Decay of the Newton potential and gradient field (BSGradFieldDecay)

Source `the November 2 reference manuscript` lines 1351-1362.

The first bound is the convolution estimate of `absConvPow` (exponent `1`) for the Newton
potential `1/(4π|x|)`; the second is `bsTestConvBound`, using `|h • K| = |h| |K|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsGradFieldDecay : BSGradFieldDecay := by
  intro h hh hhs
  obtain ⟨C1, hC1nn, hC1⟩ := absConvPow (α := 1) (by norm_num) (by norm_num) h
    hh.continuous hhs
  obtain ⟨C2, hC2⟩ := bsTestConvBound h hh.continuous hhs
  have hpi : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  refine ⟨max (max ((4 * Real.pi)⁻¹ * C1) C2) 0, fun z => ⟨?_, ?_⟩⟩
  · have hpt : ∀ y : Space,
        ‖((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * h y‖
          = (4 * Real.pi)⁻¹ * (‖h y‖ * ‖y - z‖ ^ (-(1 : ℝ))) := by
      intro y
      have hnp : UnforcedLeray.PressureAnalysis.newtonPotential (y - z)
          = (4 * Real.pi)⁻¹ * ‖y - z‖⁻¹ := by
        unfold UnforcedLeray.PressureAnalysis.newtonPotential
        rw [one_div, mul_inv]
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (UnforcedLeray.PressureAnalysis.newtonPotential_nonneg _), hnp,
        Real.rpow_neg_one]
      ring
    have hw0 : 0 ≤ (1 + ‖z‖)⁻¹ := by positivity
    have hC' : (4 * Real.pi)⁻¹ * C1 ≤ max (max ((4 * Real.pi)⁻¹ * C1) C2) 0 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hw : (1 + ‖z‖) ^ (-(1 : ℝ)) = (1 + ‖z‖)⁻¹ := Real.rpow_neg_one _
    calc ‖∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * h y‖
        ≤ ∫ y : Space, ‖((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ)
            * h y‖ := norm_integral_le_integral_norm _
      _ = ∫ y : Space, (4 * Real.pi)⁻¹ * (‖h y‖ * ‖y - z‖ ^ (-(1 : ℝ))) :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = (4 * Real.pi)⁻¹ * ∫ y : Space, ‖h y‖ * ‖y - z‖ ^ (-(1 : ℝ)) :=
          integral_const_mul _ _
      _ ≤ (4 * Real.pi)⁻¹ * (C1 * (1 + ‖z‖) ^ (-(1 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hC1 z).2 hpi
      _ = ((4 * Real.pi)⁻¹ * C1) * (1 + ‖z‖)⁻¹ := by rw [hw]; ring
      _ ≤ max (max ((4 * Real.pi)⁻¹ * C1) C2) 0 * (1 + ‖z‖)⁻¹ :=
          mul_le_mul_of_nonneg_right hC' hw0
  · have hw2 : 0 ≤ (1 + ‖z‖ ^ 2)⁻¹ := by positivity
    have hC2' : C2 ≤ max (max ((4 * Real.pi)⁻¹ * C1) C2) 0 :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    calc ‖∫ y : Space, h y • bsKernel (y - z)‖
        ≤ ∫ y : Space, ‖h y • bsKernel (y - z)‖ := norm_integral_le_integral_norm _
      _ = ∫ y : Space, ‖h y‖ * ‖bsKernel (y - z)‖ :=
          integral_congr_ae (ae_of_all _ fun y => norm_smul _ _)
      _ ≤ C2 * (1 + ‖z‖ ^ 2)⁻¹ := (hC2 z).2
      _ ≤ max (max ((4 * Real.pi)⁻¹ * C1) C2) 0 * (1 + ‖z‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hC2' hw2

end UnforcedLeray.Short.PartIIIb.Concrete
