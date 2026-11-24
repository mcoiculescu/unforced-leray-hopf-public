import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelLipschitz

/-!
# Uniform-in-time Lipschitz estimate for the actual nonlinear Duhamel term

The square-root time factor is monotone on a finite positive interval, giving the uniform
contraction coefficient needed for a Picard map on continuous H³ paths.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- Uniform finite-interval bound for the actual nonlinear Duhamel map on a bounded H³ ball.
The supremum distance of the input paths is multiplied by an explicit `√T` coefficient. -/
theorem norm_projectedHeatNonlinearityIntegral_sub_le_uniform {c ν T R δ : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hT : 0 < T) (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c))
    (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hu : ∀ r ∈ Icc 0 T, ‖u r‖ ≤ R)
    (hv : ∀ r ∈ Icc 0 T, ‖v r‖ ≤ R)
    (hδuv : ∀ r ∈ Icc 0 T, ‖u r - v r‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u t -
        projectedHeatNonlinearityIntegral (ν := ν) hc hc1 v t‖ ≤
      ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
        ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
  by_cases ht0 : t = 0
  · subst t
    have hzero₁ : projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u 0 = 0 := by
      simp [projectedHeatNonlinearityIntegral]
    have hzero₂ : projectedHeatNonlinearityIntegral (ν := ν) hc hc1 v 0 = 0 := by
      simp [projectedHeatNonlinearityIntegral]
    rw [hzero₁, hzero₂]
    simp
    positivity
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hRloc : ∀ r ∈ Ioo 0 t, ‖u r‖ ≤ R := by
      intro r hr
      apply hu r
      exact ⟨le_of_lt hr.1, le_trans (le_of_lt hr.2) ht.2⟩
    have hVloc : ∀ r ∈ Ioo 0 t, ‖v r‖ ≤ R := by
      intro r hr
      apply hv r
      exact ⟨le_of_lt hr.1, le_trans (le_of_lt hr.2) ht.2⟩
    have hδloc : ∀ r ∈ Ioo 0 t, ‖u r - v r‖ ≤ δ := by
      intro r hr
      apply hδuv r
      exact ⟨le_of_lt hr.1, le_trans (le_of_lt hr.2) ht.2⟩
    have hfixed := norm_projectedHeatNonlinearityIntegral_sub_le
      hc hν htpos hc1 u v hR hRloc hVloc hδloc
    have hpow : t ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow ht.1 ht.2 (by norm_num)
    have hcoef : 0 ≤ (3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
        UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖ := by
      positivity
    have hscale : 0 ≤ (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) := by
      positivity
    calc
      _ ≤ ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ)) := hfixed
      _ ≤ ((3072 * R * δ) * ‖(UnforcedLeray.Train.toVecL :
            UnforcedLeray.GaussianVortex.Plane →L[ℝ] UnforcedLeray.Train.Vec)‖) *
          ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hpow hscale
        · exact hcoef

#print axioms UnforcedLeray.TrainB.norm_projectedHeatNonlinearityIntegral_sub_le_uniform

end UnforcedLeray.TrainB
