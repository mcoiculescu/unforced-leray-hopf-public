import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianApprox
import UnforcedLeray.Lib.HeatCylinder.HeatVecApproxIdentity

/-!
# Age-zero approximate identity for actual vector convolution

The Minkowski estimate reduces the heat increment on the normalized cell to the Gaussian average
of translation increments. The compiled Gaussian DCT lemma makes that average vanish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

/-- On the positive-age filter, the actual Gaussian convolution of the canonical normalized-cell
representative converges to that representative in `L²`. -/
theorem tendsto_eLpNorm_heatVecConvolution_sub_zero {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    Tendsto (fun θ : ℝ => eLpNorm
      (heatVecConvolution θ (normalizedVecHeatRep hc x) - normalizedVecHeatRep hc x)
      2 (cellMeasure c)) (𝓝[>] 0) (𝓝 0) := by
  let f := normalizedVecHeatRep hc x
  let Ψ : ℝ → ℝ≥0∞ := fun θ =>
    ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
      eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2 (cellMeasure c)
  have hΨfull := tendsto_heatVecGaussianTranslationAverage_zero hc x
  have hΨ : Tendsto Ψ (𝓝 0) (𝓝 0) := by
    simpa [Ψ, f] using hΨfull
  have hfmeas : AEStronglyMeasurable f volume :=
    (normalizedVecHeatRep_measurable hc x).aestronglyMeasurable
  have hfper : UnforcedLeray.B0284.IsQPeriodic c f := normalizedVecHeatRep_periodic hc x
  have hfmem : MemLp f 2 (cellMeasure c) :=
    (memLp_congr_ae (normalizedVecHeatRep_ae hc x)).mpr (Lp.memLp x)
  have hbound : ∀ θ, 0 < θ →
      eLpNorm (heatVecConvolution θ f - f) 2 (cellMeasure c) ≤ Ψ θ := by
    intro θ hθ
    calc
      eLpNorm (heatVecConvolution θ f - f) 2 (cellMeasure c) ≤
          ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) *
            eLpNorm (fun z : Plane => f (z - w) - f z) 2 (cellMeasure c) :=
        eLpNorm_heatVecConvolution_sub_le hc hθ hfmeas hfper hfmem
      _ = Ψ θ := by
        simpa [Ψ, f] using lintegral_heatKernel2_mul_eq_unit hθ
          (fun w : Plane => eLpNorm (fun z : Plane => f (z - w) - f z)
            2 (cellMeasure c))
  let F : ℝ → ℝ≥0∞ := fun θ => if 0 < θ then
    eLpNorm (heatVecConvolution θ f - f) 2 (cellMeasure c) else 0
  have hF : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hΨ.mono_left nhdsWithin_le_nhds) (fun _ => zero_le) ?_
    intro θ
    by_cases hθ : 0 < θ
    · simpa [F, hθ] using hbound θ hθ
    · simp [F, hθ]
  have hEq : (fun θ : ℝ => eLpNorm (heatVecConvolution θ f - f) 2
      (cellMeasure c)) =ᶠ[𝓝[>] 0] F := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hpos : 0 < θ := by simpa using hθ
    simp [F, hpos]
  exact hF.congr' hEq.symm

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_eLpNorm_heatVecConvolution_sub_zero
