import UnforcedLeray.Lib.HeatCylinder.HeatL2Operator
import UnforcedLeray.Units.B0295.Kernel

/-!
# Positive-age continuity of the zero-order Gaussian heat orbit

The actual B0284 heat family has an L² quotient orbit. B0295's L¹ kernel-distance estimate gives
its strong continuity at every strictly positive heat age.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

private theorem norm_heatL2_sub_le_kernelDist {c θ θ₀ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ₀ : 0 < θ₀) (x : Lp Plane 2 (cellMeasure c)) :
    ‖heatL2 hc θ x - heatL2 hc θ₀ x‖ ≤
      (ENNReal.toReal (UnforcedLeray.B0295.kernelDist θ θ₀)) * ‖x‖ := by
  let f := planeRep hc x
  let hf := planeRep_spec hc x
  let hmem := memLp_planeRep hc x
  let hheat : ∀ s : ℝ, MemLp (UnforcedLeray.B0284.heat s f) 2 (cellMeasure c) := by
    intro s
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c s hf.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := s) hc hf.2.1
      hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
  have hheatAe : ∀ s : ℝ, (heatL2 hc s x : Plane → Plane) =ᵐ[cellMeasure c]
      UnforcedLeray.B0284.heat s f := by
    intro s
    change ((hheat s).toLp (UnforcedLeray.B0284.heat s f) : Plane → Plane) =ᵐ[
      cellMeasure c] UnforcedLeray.B0284.heat s f
    exact (hheat s).coeFn_toLp
  have hdiff : ((heatL2 hc θ x - heatL2 hc θ₀ x : Lp Plane 2 (cellMeasure c)) :
      Plane → Plane) =ᵐ[cellMeasure c]
      (UnforcedLeray.B0284.heat θ f - UnforcedLeray.B0284.heat θ₀ f) := by
    filter_upwards [Lp.coeFn_sub (heatL2 hc θ x) (heatL2 hc θ₀ x),
      hheatAe θ, hheatAe θ₀] with z hsub hθz hθ₀z
    calc
      (heatL2 hc θ x - heatL2 hc θ₀ x : Lp Plane 2 (cellMeasure c)) z =
          (heatL2 hc θ x : Plane → Plane) z - (heatL2 hc θ₀ x : Plane → Plane) z := hsub
      _ = UnforcedLeray.B0284.heat θ f z - UnforcedLeray.B0284.heat θ₀ f z := by
        rw [hθz, hθ₀z]
      _ = (UnforcedLeray.B0284.heat θ f - UnforcedLeray.B0284.heat θ₀ f) z := rfl
  have hraw := UnforcedLeray.B0295.eLpNorm_heat_sub_le hc hθ hθ₀ hf.2.1
    hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  have hκ : UnforcedLeray.B0295.kernelDist θ θ₀ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofNat_ne_top
      (UnforcedLeray.B0295.kernelDist_le_two hθ hθ₀)
  have hprod := ENNReal.mul_ne_top hκ hmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hprod hraw
  rw [ENNReal.toReal_mul] at hreal
  have hinput : ENNReal.toReal (eLpNorm f 2 (cellMeasure c)) = ‖x‖ := by
    rw [eLpNorm_congr_ae hf.2.2, Lp.norm_def]
  calc
    ‖heatL2 hc θ x - heatL2 hc θ₀ x‖ =
        ENNReal.toReal (eLpNorm
          (UnforcedLeray.B0284.heat θ f - UnforcedLeray.B0284.heat θ₀ f) 2
          (cellMeasure c)) := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae hdiff
    _ ≤ ENNReal.toReal (UnforcedLeray.B0295.kernelDist θ θ₀) * ‖x‖ := by
      rw [← hinput]
      exact hreal

/-- For every fixed normalized-cell `L²` input, the actual Gaussian heat orbit is strongly
continuous at every strictly positive heat age. -/
theorem continuousAt_heatL2_of_pos {c θ₀ : ℝ} (hc : 0 < c) (hθ₀ : 0 < θ₀)
    (x : Lp Plane 2 (cellMeasure c)) : ContinuousAt (fun θ => heatL2 hc θ x) θ₀ := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hkernel := UnforcedLeray.B0295.tendsto_kernelDist hθ₀
  have hkernelReal : Tendsto
      (fun θ : ℝ => ENNReal.toReal (UnforcedLeray.B0295.kernelDist θ θ₀))
      (𝓝 θ₀) (𝓝 0) := by
    convert (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hkernel using 1 <;> rfl
  have htop : Tendsto
      (fun θ : ℝ => ENNReal.toReal (UnforcedLeray.B0295.kernelDist θ θ₀) * ‖x‖)
      (𝓝 θ₀) (𝓝 0) := by
    simpa using hkernelReal.mul_const ‖x‖
  have hupper : ∀ᶠ θ in 𝓝 θ₀,
      dist (heatL2 hc θ x) (heatL2 hc θ₀ x) ≤
        ENNReal.toReal (UnforcedLeray.B0295.kernelDist θ θ₀) * ‖x‖ := by
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    rw [dist_eq_norm]
    exact norm_heatL2_sub_le_kernelDist hc hθ hθ₀ x
  have hdist := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 θ₀) (𝓝 0)) htop
    (Filter.Eventually.of_forall fun _ => dist_nonneg) hupper
  simpa using hdist

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuousAt_heatL2_of_pos
