import UnforcedLeray.Lib.HeatCylinder.KernelOrbitL2
import UnforcedLeray.Lib.HeatCylinder.OrbitCLM
import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit

/-!
# Positive-age continuity of the actual normalized-cell heat orbit

The L¹ continuity of the concrete Gaussian-gradient kernel and periodic Minkowski give strong
continuity of its actual cylinder L² output at every positive heat age.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

private theorem norm_heatDivL2Orbit_sub_le {c θ θ₀ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hmeas : Measurable T)
    (hmem : MemLp T 2 (cellMeasure c)) :
    ‖heatDivL2Orbit hc hper hmeas hmem θ - heatDivL2Orbit hc hper hmeas hmem θ₀‖ ≤
      (∫ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) *
        ‖hmem.toLp T‖ := by
  let outθ := periodicHeatDivMemLp hc hθ T hper hmeas.aestronglyMeasurable hmem
  let outθ₀ := periodicHeatDivMemLp hc hθ₀ T hper hmeas.aestronglyMeasurable hmem
  let diffMem := outθ.sub outθ₀
  have hclass : heatDivL2Orbit hc hper hmeas hmem θ -
      heatDivL2Orbit hc hper hmeas hmem θ₀ =
      diffMem.toLp (UnforcedLeray.B0296.heatDiv θ T -
        UnforcedLeray.B0296.heatDiv θ₀ T) := by
    rw [heatDivL2Orbit_eq_CLM hc hθ hper hmeas hmem,
      heatDivL2Orbit_eq_CLM hc hθ₀ hper hmeas hmem,
      heatDivL2CLM_apply_to_periodic hc hθ hper hmeas.aestronglyMeasurable hmem,
      heatDivL2CLM_apply_to_periodic hc hθ₀ hper hmeas.aestronglyMeasurable hmem]
    apply Lp.ext
    filter_upwards [outθ.coeFn_toLp, outθ₀.coeFn_toLp, diffMem.coeFn_toLp,
      Lp.coeFn_sub (outθ.toLp (UnforcedLeray.B0296.heatDiv θ T))
        (outθ₀.toLp (UnforcedLeray.B0296.heatDiv θ₀ T))] with z hθz hθ₀z hdz hsub
    calc
      (outθ.toLp (UnforcedLeray.B0296.heatDiv θ T) -
          outθ₀.toLp (UnforcedLeray.B0296.heatDiv θ₀ T)) z =
          outθ.toLp (UnforcedLeray.B0296.heatDiv θ T) z -
            outθ₀.toLp (UnforcedLeray.B0296.heatDiv θ₀ T) z := hsub
      _ = UnforcedLeray.B0296.heatDiv θ T z -
          UnforcedLeray.B0296.heatDiv θ₀ T z := by rw [hθz, hθ₀z]
      _ = (UnforcedLeray.B0296.heatDiv θ T -
          UnforcedLeray.B0296.heatDiv θ₀ T) z := rfl
      _ = diffMem.toLp (UnforcedLeray.B0296.heatDiv θ T -
          UnforcedLeray.B0296.heatDiv θ₀ T) z := hdz.symm
  have hnorm : ‖diffMem.toLp (UnforcedLeray.B0296.heatDiv θ T -
      UnforcedLeray.B0296.heatDiv θ₀ T)‖ =
      ENNReal.toReal (eLpNorm (UnforcedLeray.B0296.heatDiv θ T -
        UnforcedLeray.B0296.heatDiv θ₀ T) 2 (cellMeasure c)) := by
    rw [Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae diffMem.coeFn_toLp
  have hdiff := eLpNorm_heatDiv_timeDiff_le hc hθ hθ₀ hper
    hmeas.aestronglyMeasurable hmem
  have htop : ENNReal.ofReal (∫ w : Plane,
      ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) *
        eLpNorm T 2 (cellMeasure c) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hdiff
  have hmass_nonneg : 0 ≤ ∫ w : Plane,
      ‖divKernelCLM θ w - divKernelCLM θ₀ w‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hinputNorm : (eLpNorm T 2 (cellMeasure c)).toReal = ‖hmem.toLp T‖ := by
    calc
      _ = (eLpNorm (hmem.toLp T : Plane → Plane × Plane) 2
          (cellMeasure c)).toReal := by
        congr 1
        exact eLpNorm_congr_ae hmem.coeFn_toLp.symm
      _ = _ := (Lp.norm_def _).symm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hmass_nonneg, hinputNorm] at hreal
  rw [hclass, hnorm]
  exact hreal

/-- The actual B0296 heat-divergence orbit is strongly continuous in the normalized-cell L²
quotient at every positive heat age. -/
theorem continuousAt_heatDivL2Orbit {c θ₀ : ℝ} (hc : 0 < c) (hθ₀ : 0 < θ₀)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T) (hmeas : Measurable T)
    (hmem : MemLp T 2 (cellMeasure c)) :
    ContinuousAt (heatDivL2Orbit hc hper hmeas hmem) θ₀ := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hkernel := tendsto_integral_norm_divKernelCLM_sub hθ₀
  have htop : Tendsto
      (fun θ : ℝ => (∫ w : Plane,
        ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) * ‖hmem.toLp T‖)
      (𝓝 θ₀) (𝓝 0) := by
    simpa using hkernel.mul_const ‖hmem.toLp T‖
  have hupper : ∀ᶠ θ in 𝓝 θ₀,
      dist (heatDivL2Orbit hc hper hmeas hmem θ)
        (heatDivL2Orbit hc hper hmeas hmem θ₀) ≤
      (∫ w : Plane, ‖divKernelCLM θ w - divKernelCLM θ₀ w‖) * ‖hmem.toLp T‖ := by
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    rw [dist_eq_norm]
    exact norm_heatDivL2Orbit_sub_le hc hθ hθ₀ hper hmeas hmem
  have hdist := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 θ₀) (𝓝 0)) htop
    (Filter.Eventually.of_forall fun _ => dist_nonneg) hupper
  simpa using hdist

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuousAt_heatDivL2Orbit
