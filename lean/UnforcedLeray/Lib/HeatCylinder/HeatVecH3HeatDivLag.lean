import UnforcedLeray.Lib.HeatCylinder.HeatVecH3HeatDivComposition
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup

/-!
# Nonnegative-lag ordinary heat after positive-age heat-divergence

This is the operator form used when splitting actual cylinder Duhamel integrands. The heat-divergence
age remains strictly positive; the ordinary heat lag may be zero and uses the actual identity branch.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

/-- Pointwise nonnegative-lag splitting of the actual ordinary H³ heat after the positive-age
actual H³ heat-divergence response. -/
theorem heatVecH3Semigroup_apply_actualHeatDivH3_of_nonneg {c α β : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α) (hβ : 0 < β)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    heatVecH3Semigroup (c := c) (θ := α) hc (actualHeatDivH3 hc hβ x) =
      actualHeatDivH3 hc (add_pos_of_nonneg_of_pos hα hβ) x := by
  by_cases hαpos : 0 < α
  · rw [heatVecH3Semigroup_apply_of_pos hc hαpos]
    simpa only [actualHeatVecH3CLM_apply] using
      actualHeatVecH3_comp_actualHeatDivH3 hc hαpos hβ x
  · have hαzero : α = 0 := le_antisymm (not_lt.mp hαpos) hα
    subst α
    rw [heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl (0 : ℝ)),
      ContinuousLinearMap.id_apply]
    simpa only [zero_add]

/-- Operator form of the nonnegative-lag composition identity, suitable for postcomposing an
actual H³ Bochner integrand. -/
theorem heatVecH3Semigroup_comp_actualHeatDivH3CLM_of_nonneg {c α β : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α) (hβ : 0 < β) :
    (heatVecH3Semigroup (c := c) (θ := α) hc).comp
      (actualHeatDivH3CLM hc hβ) =
      actualHeatDivH3CLM hc (add_pos_of_nonneg_of_pos hα hβ) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, actualHeatDivH3CLM_apply]
  exact heatVecH3Semigroup_apply_actualHeatDivH3_of_nonneg hc hα hβ x

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_apply_actualHeatDivH3_of_nonneg
#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_comp_actualHeatDivH3CLM_of_nonneg
