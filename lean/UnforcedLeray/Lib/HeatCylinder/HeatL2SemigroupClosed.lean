import UnforcedLeray.Lib.HeatCylinder.HeatL2Linearity

/-!
# Identity and closed nonnegative-time semigroup law for cylinder `L²` heat

This closes the time endpoint using the actual nonpositive-age convention in B0284. The positive
interior composition identity is the Gaussian kernel law already established in B0289.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.GaussianVortex (Plane)

/-- At zero heat age the descended actual Gaussian family is the identity on normalized-cell
`L²`. -/
theorem heatL2_zero {c : ℝ} (hc : 0 < c) (x : Lp Plane 2 (cellMeasure c)) :
    heatL2 hc 0 x = x :=
  heatL2_eq_id_of_nonpos hc le_rfl x

/-- The actual cylinder Gaussian family is a semigroup on nonnegative heat ages, including the
identity endpoint. -/
theorem heatL2_comp_of_nonneg {c α β : ℝ} (hc : 0 < c) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (x : Lp Plane 2 (cellMeasure c)) :
    heatL2 hc α (heatL2 hc β x) = heatL2 hc (α + β) x := by
  rcases hα.eq_or_lt with hα0 | hαpos
  · subst α
    rw [heatL2_zero hc, zero_add]
  rcases hβ.eq_or_lt with hβ0 | hβpos
  · subst β
    rw [heatL2_zero hc, add_zero]
  exact heatL2_comp_of_pos hc hαpos hβpos x

/-- Semigroup composition as an equality of the actual normalized-cell heat CLMs. -/
theorem heatL2CLM_comp_of_nonneg {c α β : ℝ} (hc : 0 < c)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (heatL2CLM hc α).comp (heatL2CLM hc β) = heatL2CLM hc (α + β) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, heatL2CLM_apply]
  exact heatL2_comp_of_nonneg hc hα hβ x

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatL2_comp_of_nonneg
#print axioms UnforcedLeray.HeatCylinder.heatL2CLM_comp_of_nonneg
