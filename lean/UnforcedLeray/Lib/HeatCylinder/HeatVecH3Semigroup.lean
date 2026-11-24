import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2Semigroup

/-!
# Actual centered vector H³ Gaussian heat semigroup

At nonpositive ages the family is the identity, matching the actual heat convention. At positive
ages it is the completed actual Gaussian convolution operator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- The actual vector Gaussian heat family on centered H³, with the identity convention at
nonpositive ages. -/
noncomputable def heatVecH3Semigroup {c θ : ℝ} (hc : 0 < c) :
    UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ] UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
  if hθ : 0 < θ then actualHeatVecH3CLM hc hθ
  else ContinuousLinearMap.id ℝ _

@[simp] theorem heatVecH3Semigroup_apply_of_pos {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    heatVecH3Semigroup (c := c) (θ := θ) hc x = actualHeatVecH3CLM hc hθ x := by
  simp [heatVecH3Semigroup, hθ]

@[simp] theorem heatVecH3Semigroup_eq_id_of_nonpos {c θ : ℝ} (hc : 0 < c)
    (hθ : θ ≤ 0) :
    heatVecH3Semigroup (c := c) (θ := θ) hc = ContinuousLinearMap.id ℝ _ := by
  have hn : ¬ 0 < θ := not_lt.mpr hθ
  simp [heatVecH3Semigroup, hn]

/-- The actual centered H³ Gaussian heat family satisfies the semigroup law at nonnegative ages.
-/
theorem heatVecH3Semigroup_comp_of_nonneg {c α β : ℝ} (hc : 0 < c)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (heatVecH3Semigroup (c := c) (θ := α) hc).comp
      (heatVecH3Semigroup (c := c) (θ := β) hc) =
      heatVecH3Semigroup (c := c) (θ := α + β) hc := by
  by_cases hαpos : 0 < α
  · by_cases hβpos : 0 < β
    · apply ContinuousLinearMap.ext
      intro x
      rw [ContinuousLinearMap.comp_apply]
      apply vectorH3NormalizedValue_injective hc
      rw [heatVecH3Semigroup_apply_of_pos (c := c) (θ := α) hc hαpos,
        heatVecH3Semigroup_apply_of_pos (c := c) (θ := β) hc hβpos,
        heatVecH3Semigroup_apply_of_pos (c := c) (θ := α + β) hc
          (add_pos hαpos hβpos)]
      simp only [actualHeatVecH3CLM_apply]
      rw [vectorH3NormalizedValue_actualHeatVecH3 hc hαpos,
        vectorH3NormalizedValue_actualHeatVecH3 hc hβpos,
        vectorH3NormalizedValue_actualHeatVecH3 hc (add_pos hαpos hβpos)]
      rw [← ContinuousLinearMap.comp_apply]
      rw [← heatVecL2CLM_comp_of_nonneg hc hα hβ]
    · have hβzero : β = 0 := le_antisymm (not_lt.mp hβpos) hβ
      subst β
      rw [heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl (0 : ℝ)),
        ContinuousLinearMap.comp_id]
      rw [add_zero]
  · have hαzero : α = 0 := le_antisymm (not_lt.mp hαpos) hα
    subst α
    rw [heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl (0 : ℝ)),
      ContinuousLinearMap.id_comp]
    rw [zero_add]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_comp_of_nonneg
