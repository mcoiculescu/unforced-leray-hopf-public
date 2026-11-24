import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ProjectedHeatDivIntegral
import UnforcedLeray.Lib.HeatCylinder.H3RoughOrbitContinuity

/-!
# Actual projected heat-divergence orbit under an outer heat lag

This form uses the actual positive-age/zero-otherwise Gaussian response orbit and only requires
positivity of its age almost everywhere on the integration domain. It therefore matches open-time
Duhamel integrals, whose endpoint ages are irrelevant null sets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Set

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.TrainB (P0H3CLM)

/-- An actual nonnegative-lag ordinary heat passes through a Bochner integral of projected actual
heat-divergence orbits, adding the lag to the response age wherever that age is positive. -/
theorem heatVecH3Semigroup_integral_P0_actualHeatDivH3Orbit_of_ae_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c α : ℝ} (hc : 0 < c) (hα : 0 ≤ α)
    (F : Ω → UnforcedLeray.TrainB.TensorH3 c) (β : Ω → ℝ)
    (hβ : ∀ᵐ ω ∂μ, 0 < β ω)
    (hF : Integrable (fun ω => P0H3CLM hc
      (actualHeatDivH3Orbit hc (F ω) (β ω))) μ) :
    heatVecH3Semigroup (c := c) (θ := α) hc
      (∫ ω, P0H3CLM hc (actualHeatDivH3Orbit hc (F ω) (β ω)) ∂μ) =
    ∫ ω, P0H3CLM hc (actualHeatDivH3Orbit hc (F ω) (α + β ω)) ∂μ := by
  calc
    heatVecH3Semigroup (c := c) (θ := α) hc
        (∫ ω, P0H3CLM hc (actualHeatDivH3Orbit hc (F ω) (β ω)) ∂μ) =
      ∫ ω, heatVecH3Semigroup (c := c) (θ := α) hc
        (P0H3CLM hc (actualHeatDivH3Orbit hc (F ω) (β ω))) ∂μ :=
          (heatVecH3Semigroup (c := c) (θ := α) hc).integral_comp_comm hF |>.symm
    _ = ∫ ω, P0H3CLM hc
        (actualHeatDivH3Orbit hc (F ω) (α + β ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hβ] with ω hβω
      have hpoint := heatVecH3Semigroup_P0H3CLM_actualHeatDivH3_of_nonneg
        hc hα hβω (F ω)
      simpa only [actualHeatDivH3Orbit, dif_pos hβω,
        dif_pos (add_pos_of_nonneg_of_pos hα hβω), actualHeatDivH3CLM_apply] using hpoint

/-- Exact source-time splitting for the actual projected H³ Duhamel response. For `a<s≤t` and
positive viscosity, propagating the response from time `s` to time `t` adds the lag
`ν(t-s)` to the literal B0296 heat-divergence age `ν(s-r)`, yielding `ν(t-r)`. -/
theorem heatVecH3Semigroup_integral_projectedDuhamelLag
    {a s t ν c : ℝ} (hc : 0 < c) (hν : 0 < ν) (hst : s ≤ t)
    (F : ℝ → UnforcedLeray.TrainB.TensorH3 c)
    (hF : Integrable (fun r => P0H3CLM hc
      (actualHeatDivH3Orbit hc (F r) (ν * (s - r))))
      (volume.restrict (Ioo a s))) :
    heatVecH3Semigroup (c := c) (θ := ν * (t - s)) hc
      (∫ r in Ioo a s, P0H3CLM hc
        (actualHeatDivH3Orbit hc (F r) (ν * (s - r))) ∂volume) =
    ∫ r in Ioo a s, P0H3CLM hc
      (actualHeatDivH3Orbit hc (F r) (ν * (t - r))) ∂volume := by
  have hα : 0 ≤ ν * (t - s) := mul_nonneg hν.le (sub_nonneg.mpr hst)
  have hβ : ∀ᵐ r ∂volume.restrict (Ioo a s), 0 < ν * (s - r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_pos hν (sub_pos.mpr hr.2)
  have hcore := heatVecH3Semigroup_integral_P0_actualHeatDivH3Orbit_of_ae_pos
    hc hα F (fun r => ν * (s - r)) hβ hF
  have hright : (fun r : ℝ => P0H3CLM hc
      (actualHeatDivH3Orbit hc (F r) (ν * (t - r)))) =ᵐ[
        volume.restrict (Ioo a s)]
      (fun r => P0H3CLM hc
        (actualHeatDivH3Orbit hc (F r) (ν * (t - s) + ν * (s - r)))) := by
    filter_upwards with r
    congr 2
    ring
  calc
    heatVecH3Semigroup (c := c) (θ := ν * (t - s)) hc
        (∫ r in Ioo a s, P0H3CLM hc
          (actualHeatDivH3Orbit hc (F r) (ν * (s - r))) ∂volume) =
      ∫ r in Ioo a s, P0H3CLM hc
        (actualHeatDivH3Orbit hc (F r) (ν * (t - s) + ν * (s - r))) ∂volume := by
          simpa using hcore
    _ = ∫ r in Ioo a s, P0H3CLM hc
        (actualHeatDivH3Orbit hc (F r) (ν * (t - r))) ∂volume :=
          integral_congr_ae hright.symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_integral_P0_actualHeatDivH3Orbit_of_ae_pos
#print axioms UnforcedLeray.HeatCylinder.heatVecH3Semigroup_integral_projectedDuhamelLag
