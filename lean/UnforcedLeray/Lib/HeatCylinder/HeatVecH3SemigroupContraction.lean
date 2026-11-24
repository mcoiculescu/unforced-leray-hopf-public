import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator

/-!
# Contraction of the actual centered H³ Gaussian family

The positive-age branch is the concrete Gaussian heat CLM and the nonpositive branch is the
identity; both have operator norm at most one.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- The actual centered H³ heat family has operator norm at most one at every real age. -/
theorem norm_heatVecH3Semigroup_le_one {c θ : ℝ} (hc : 0 < c) :
    ‖heatVecH3Semigroup (c := c) (θ := θ) hc‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · simpa [heatVecH3Semigroup, hθ] using norm_actualHeatVecH3CLM_le_one hc hθ
  · simpa [heatVecH3Semigroup, hθ] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ)
        (E := UnforcedLeray.Cyl.H ℝ Vec c 0 3))

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.norm_heatVecH3Semigroup_le_one
