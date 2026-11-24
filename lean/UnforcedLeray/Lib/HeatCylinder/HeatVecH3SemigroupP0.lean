import UnforcedLeray.Lib.HeatCylinder.HeatVecH3P0Compatibility
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup

/-!
# Leray compatibility for the full age-indexed H³ heat family

The positive-age actual Gaussian heat commutes with the actual H³ Leray projection. At
nonpositive ages the defined heat family is the identity, so the same compatibility holds for
every real age, including the zero-age trace.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

/-- The actual H³ heat family, including its identity convention at nonpositive ages, commutes
with the actual TrainB H³ Leray projection. -/
theorem heatVecH3Semigroup_P0H3CLM_comm {c θ : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    UnforcedLeray.TrainB.P0H3CLM hc (heatVecH3Semigroup (c := c) (θ := θ) hc x) =
      heatVecH3Semigroup (c := c) (θ := θ) hc (UnforcedLeray.TrainB.P0H3CLM hc x) := by
  by_cases hθ : 0 < θ
  · simpa [heatVecH3Semigroup, hθ] using
      actualHeatVecH3_P0H3CLM_comm hc hθ x
  · have hθ' : θ ≤ 0 := le_of_not_gt hθ
    rw [heatVecH3Semigroup_eq_id_of_nonpos (c := c) (θ := θ) hc hθ']
    rfl

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_P0H3CLM_comm
