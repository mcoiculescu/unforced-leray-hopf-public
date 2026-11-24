import UnforcedLeray.Lib.TrainB.DatumHeatSeedMild
import UnforcedLeray.Lib.TrainB.DatumHeatH3OperatorBridge

set_option autoImplicit false

namespace UnforcedLeray.TrainB

/-- At every positive train age, the seed path is the H³ class of the literal Gaussian
convolution of the actual periodized datum. -/
theorem datumHeatSeedPath_eq_literal_gaussian {c ν t : ℝ}
    (hc2 : 2 ≤ c) (hν : 0 < ν) (ht : 0 < t) :
    datumHeatSeedPath (by linarith : 0 < c) hν t =
      datumHeatVecH3 hc2 (mul_pos hν ht) := by
  have hc : 0 < c := by linarith
  have hθ : 0 < ν * t := mul_pos hν ht
  change HeatCylinder.heatVecH3Semigroup (c := c)
      (θ := max 0 (ν * t)) hc (datumVecH3 hc) = _
  rw [max_eq_right (le_of_lt hθ)]
  rw [HeatCylinder.heatVecH3Semigroup_apply_of_pos hc hθ]
  exact (datumHeatVecH3_eq_actualHeatVecH3 hc2 hθ).symm

#print axioms UnforcedLeray.TrainB.datumHeatSeedPath_eq_literal_gaussian

end UnforcedLeray.TrainB
