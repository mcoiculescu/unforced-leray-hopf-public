import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelEstimate

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.TrainB

/-- The actual projected Gaussian Duhamel integral at time `t` depends only on the velocity path
on its causal interval `(0,t)`. -/
theorem projectedHeatNonlinearityIntegral_congr_of_eq_on_causal_interval
    {c ν t : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c)
    (u v : ContinuousMap ℝ (VectorH3 c))
    (heq : ∀ r ∈ Ioo (0 : ℝ) t, u r = v r) :
    projectedHeatNonlinearityIntegral (ν := ν) hc hc1 u t =
      projectedHeatNonlinearityIntegral (ν := ν) hc hc1 v t := by
  unfold projectedHeatNonlinearityIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hstress : tensorH3StressPath hc1 u r = tensorH3StressPath hc1 v r := by
    change tensorH3Bilinear hc1 (u r) (u r) = tensorH3Bilinear hc1 (v r) (v r)
    rw [heq r hr]
  simp [projectedHeatDuhamelOrbit, hstress]

#print axioms UnforcedLeray.TrainB.projectedHeatNonlinearityIntegral_congr_of_eq_on_causal_interval

end UnforcedLeray.TrainB
