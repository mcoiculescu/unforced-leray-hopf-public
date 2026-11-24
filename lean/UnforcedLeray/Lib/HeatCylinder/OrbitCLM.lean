import UnforcedLeray.Lib.HeatCylinder.OrbitMeasurable

/-!
# Positive-time orbit identification with the descended Gaussian CLM

The measurable heat-age path agrees pointwise in age with the already-descended `L²` Gaussian
operator whenever the age is positive. This exposes the operator bound directly on the orbit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- At positive age, the measurable orbit class is the actual descended Gaussian `L²` operator
applied to the input class. -/
theorem heatDivL2Orbit_eq_CLM {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : Measurable T) (hmem : MemLp T 2
      (UnforcedLeray.B0284.cellMeasure c)) :
    heatDivL2Orbit hc hper hmeas hmem θ =
      heatDivL2CLM hc hθ (hmem.toLp T) := by
  rw [heatDivL2CLM_apply_to_periodic hc hθ hper hmeas.aestronglyMeasurable hmem]
  apply Lp.ext
  filter_upwards [
    (memLp_heatDiv_timePath hc
      (hmeas.comp measurable_snd)
      (fun _ => hper)
      (fun _ => hmem) θ (ν := -1) (s := 0)).coeFn_toLp,
    (periodicHeatDivMemLp hc hθ T hper hmeas.aestronglyMeasurable hmem).coeFn_toLp]
    with z hpath hout
  simp only [Function.comp_apply] at hpath
  calc
    (heatDivL2Orbit hc hper hmeas hmem θ) z =
        UnforcedLeray.B0296.heatDiv θ T z := by
      simpa only [heatDivL2Orbit, show (-1 : ℝ) * (0 - θ) = θ by ring] using hpath
    _ = ((periodicHeatDivMemLp hc hθ T hper hmeas.aestronglyMeasurable hmem).toLp
        (UnforcedLeray.B0296.heatDiv θ T)) z := hout.symm

/-- The positive-age normalized-cell orbit inherits the concrete Gaussian-gradient operator norm
bound. -/
theorem norm_heatDivL2Orbit_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : Measurable T) (hmem : MemLp T 2
      (UnforcedLeray.B0284.cellMeasure c)) :
    ‖heatDivL2Orbit hc hper hmeas hmem θ‖ ≤
      heatDivL2Coeff θ * ‖hmem.toLp T‖ := by
  rw [heatDivL2Orbit_eq_CLM hc hθ hper hmeas hmem]
  exact norm_heatDivL2_le hc hθ (hmem.toLp T)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatDivL2Orbit_eq_CLM
#print axioms UnforcedLeray.HeatCylinder.norm_heatDivL2Orbit_le
