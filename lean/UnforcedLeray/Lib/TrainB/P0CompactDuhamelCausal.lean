import UnforcedLeray.Lib.TrainB.P0GaussianDuhamelCausalCongr
import UnforcedLeray.Lib.TrainB.P0CompactNonlinearDuhamel

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- Two compact-time implementations of the nonlinear map agree at t whenever their clamped
velocity paths agree on the causal interval `(0,t)`. -/
theorem projectedNonlinearDuhamelCompactMap_eq_of_clamped_paths_eq_causal
    {c ν T S t : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν)
    (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (v : ContinuousMap (Icc (0 : ℝ) S) (VectorH3 c))
    (htT : t ∈ Icc (0 : ℝ) T) (htS : t ∈ Icc (0 : ℝ) S)
    (hpath : ∀ r ∈ Ioo (0 : ℝ) t,
      extendCompactPath hT u r = extendCompactPath hS v r) :
    projectedNonlinearDuhamelCompactMap hc hc1 hν hT u ⟨t, htT⟩ =
      projectedNonlinearDuhamelCompactMap hc hc1 hν hS v ⟨t, htS⟩ := by
  rw [projectedNonlinearDuhamelCompactMap_apply,
    projectedNonlinearDuhamelCompactMap_apply]
  apply congrArg Neg.neg
  apply projectedHeatNonlinearityIntegral_congr_of_eq_on_causal_interval hc hc1
  intro r hr
  exact hpath r hr

#print axioms UnforcedLeray.TrainB.projectedNonlinearDuhamelCompactMap_eq_of_clamped_paths_eq_causal

end UnforcedLeray.TrainB
