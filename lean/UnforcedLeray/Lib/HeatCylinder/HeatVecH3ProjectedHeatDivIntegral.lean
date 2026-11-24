import UnforcedLeray.Lib.HeatCylinder.HeatVecH3HeatDivIntegral
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupP0

/-!
# Projected actual H³ heat-divergence Duhamel splitting

The actual H³ Leray projection commutes with the actual ordinary heat semigroup. Combining that
fact with positive-age Gaussian heat-divergence covariance moves an outer heat lag through a
projected actual Duhamel integral without changing the divergence sign or response.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.TrainB (P0H3CLM)

/-- Pointwise nonnegative-lag splitting for the actual projected heat-divergence response. -/
theorem heatVecH3Semigroup_P0H3CLM_actualHeatDivH3_of_nonneg {c α β : ℝ}
    (hc : 0 < c) (hα : 0 ≤ α) (hβ : 0 < β)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    heatVecH3Semigroup (c := c) (θ := α) hc
        (P0H3CLM hc (actualHeatDivH3 hc hβ x)) =
      P0H3CLM hc (actualHeatDivH3 hc (add_pos_of_nonneg_of_pos hα hβ) x) := by
  calc
    heatVecH3Semigroup (c := c) (θ := α) hc
        (P0H3CLM hc (actualHeatDivH3 hc hβ x)) =
      P0H3CLM hc (heatVecH3Semigroup (c := c) (θ := α) hc
        (actualHeatDivH3 hc hβ x)) :=
          (heatVecH3Semigroup_P0H3CLM_comm hc _).symm
    _ = P0H3CLM hc
        (actualHeatDivH3 hc (add_pos_of_nonneg_of_pos hα hβ) x) := by
          exact congrArg (P0H3CLM hc)
            (heatVecH3Semigroup_apply_actualHeatDivH3_of_nonneg hc hα hβ x)

/-- Moving a nonnegative-lag actual H³ heat through a Bochner integral of projected actual
positive-age heat-divergence responses adds that lag to every literal response age. -/
theorem heatVecH3Semigroup_integral_P0H3CLM_actualHeatDivH3CLM_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c α : ℝ} (hc : 0 < c) (hα : 0 ≤ α)
    (F : Ω → UnforcedLeray.TrainB.TensorH3 c) (β : Ω → ℝ)
    (hβ : ∀ ω, 0 < β ω)
    (hF : Integrable (fun ω => P0H3CLM hc
      (actualHeatDivH3CLM hc (hβ ω) (F ω))) μ) :
    heatVecH3Semigroup (c := c) (θ := α) hc
      (∫ ω, P0H3CLM hc (actualHeatDivH3CLM hc (hβ ω) (F ω)) ∂μ) =
    ∫ ω, P0H3CLM hc (actualHeatDivH3CLM hc
      (add_pos_of_nonneg_of_pos hα (hβ ω)) (F ω)) ∂μ := by
  calc
    heatVecH3Semigroup (c := c) (θ := α) hc
        (∫ ω, P0H3CLM hc (actualHeatDivH3CLM hc (hβ ω) (F ω)) ∂μ) =
      ∫ ω, heatVecH3Semigroup (c := c) (θ := α) hc
        (P0H3CLM hc (actualHeatDivH3CLM hc (hβ ω) (F ω))) ∂μ :=
          (heatVecH3Semigroup (c := c) (θ := α) hc).integral_comp_comm hF |>.symm
    _ = ∫ ω, P0H3CLM hc (actualHeatDivH3CLM hc
        (add_pos_of_nonneg_of_pos hα (hβ ω)) (F ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      simpa only [actualHeatDivH3CLM_apply] using
        heatVecH3Semigroup_P0H3CLM_actualHeatDivH3_of_nonneg
          hc hα (hβ ω) (F ω)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_P0H3CLM_actualHeatDivH3_of_nonneg
#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_integral_P0H3CLM_actualHeatDivH3CLM_of_nonneg
