import UnforcedLeray.Lib.HeatCylinder.HeatVecH3HeatDivLag

/-!
# Splitting actual H³ heat-divergence Bochner integrals

The actual heat semigroup passes through a Bochner integral of actual positive-age heat-divergence
responses. The only integrability premise is the one needed to define the source integral; the
output integrability follows from boundedness of the actual heat CLM and the pointwise lag identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

/-- For any Bochner-integrable actual positive-age H³ heat-divergence path, an actual
nonnegative-lag ordinary heat can be moved inside the integral and added to each response age. -/
theorem heatVecH3Semigroup_integral_actualHeatDivH3CLM_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c α : ℝ} (hc : 0 < c) (hα : 0 ≤ α)
    (F : Ω → UnforcedLeray.TrainB.TensorH3 c) (β : Ω → ℝ)
    (hβ : ∀ ω, 0 < β ω)
    (hF : Integrable (fun ω => actualHeatDivH3CLM hc (hβ ω) (F ω)) μ) :
    heatVecH3Semigroup (c := c) (θ := α) hc
      (∫ ω, actualHeatDivH3CLM hc (hβ ω) (F ω) ∂μ) =
    ∫ ω, actualHeatDivH3CLM hc
      (add_pos_of_nonneg_of_pos hα (hβ ω)) (F ω) ∂μ := by
  calc
    heatVecH3Semigroup (c := c) (θ := α) hc
        (∫ ω, actualHeatDivH3CLM hc (hβ ω) (F ω) ∂μ) =
      ∫ ω, heatVecH3Semigroup (c := c) (θ := α) hc
        (actualHeatDivH3CLM hc (hβ ω) (F ω)) ∂μ :=
          (heatVecH3Semigroup (c := c) (θ := α) hc).integral_comp_comm hF |>.symm
    _ = ∫ ω, actualHeatDivH3CLM hc
        (add_pos_of_nonneg_of_pos hα (hβ ω)) (F ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      have hcomp := heatVecH3Semigroup_comp_actualHeatDivH3CLM_of_nonneg
        hc hα (hβ ω)
      have happly := congrArg (fun L => L (F ω)) hcomp
      simpa only [ContinuousLinearMap.comp_apply] using happly

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_integral_actualHeatDivH3CLM_of_nonneg
