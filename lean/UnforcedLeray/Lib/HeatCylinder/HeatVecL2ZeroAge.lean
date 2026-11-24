import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolutionZeroAge
import UnforcedLeray.Lib.HeatCylinder.HeatVecActualContraction

/-!
# Strong continuity at zero for the actual normalized-cell vector heat

The Gaussian approximate-identity estimate is transported from the canonical periodic
representative to the genuine quotient-valued heat operator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

private theorem ae_heatVecTranslationIncrement_of_global_ae {c : ℝ} (_hc : 0 < c)
    {f g : Plane → Vec} (hfg : f =ᵐ[volume] g) (w : Plane) :
    (fun z : Plane => f (z - w) - f z) =ᵐ[cellMeasure c]
      fun z => g (z - w) - g z := by
  have hshiftVol := (measurePreserving_add_right volume (-w)).quasiMeasurePreserving.ae hfg
  have hshiftCell : (fun z : Plane => f (z - w)) =ᵐ[cellMeasure c]
      fun z => g (z - w) := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hshiftVol)
  have hbaseCell : f =ᵐ[cellMeasure c] g := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hfg)
  filter_upwards [hshiftCell, hbaseCell] with z hzshift hzbase
  simpa only [sub_eq_add_neg] using congrArg₂ (fun a b : Vec => a - b) hzshift hzbase

private theorem lintegral_heatVecTranslationAverage_congr {c : ℝ} (hc : 0 < c)
    {f g : Plane → Vec} (hfg : f =ᵐ[volume] g) (a : ℝ) :
    (∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
      eLpNorm (fun z : Plane => f (z - a • w) - f z) 2 (cellMeasure c)) =
    ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
      eLpNorm (fun z : Plane => g (z - a • w) - g z) 2 (cellMeasure c) := by
  refine lintegral_congr fun w => ?_
  rw [eLpNorm_congr_ae (ae_heatVecTranslationIncrement_of_global_ae hc hfg (a • w))]

private theorem tendsto_heatVecGaussianAverage_of_ae_congr {c : ℝ} (hc : 0 < c)
    {f g : Plane → Vec} (hfg : f =ᵐ[volume] g)
    (hF : Tendsto (fun θ : ℝ =>
      ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
        eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2
          (cellMeasure c)) (𝓝 0) (𝓝 0)) :
    Tendsto (fun θ : ℝ =>
      ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
        eLpNorm (fun z : Plane => g (z - Real.sqrt θ • w) - g z) 2
          (cellMeasure c)) (𝓝 0) (𝓝 0) := by
  convert hF using 1
  funext θ
  exact (lintegral_heatVecTranslationAverage_congr hc hfg (Real.sqrt θ)).symm

/-- The actual normalized-cell Euclidean-vector heat quotient converges strongly to the identity
at age zero through positive ages. -/
theorem tendsto_heatVecL2CLM_apply_zero {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    Tendsto (fun θ : ℝ => heatVecL2CLM hc θ x) (𝓝[>] 0) (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let g : Plane → Vec := normalizedPlaneVecRep hc xP
  let f : Plane → Vec := normalizedVecHeatRep hc x
  have hfg : g =ᵐ[volume] f :=
    (normalizedVecHeatRep_eq_normalizedPlaneVecRep_ae hc x).symm
  have hinput : g =ᵐ[cellMeasure c] (x : Plane → Vec) := by
    have hfgCell : g =ᵐ[cellMeasure c] f := by
      apply ae_iff.mpr
      exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hfg)
    exact hfgCell.trans (normalizedVecHeatRep_ae hc x)
  have hgmeas : AEStronglyMeasurable g volume :=
    (normalizedPlaneVecRep_measurable hc xP).aestronglyMeasurable
  have hgper : UnforcedLeray.B0284.IsQPeriodic c g := by
    exact normalizedPlaneVecRep_periodic hc xP
  have hgmem : MemLp g 2 (cellMeasure c) :=
    (memLp_congr_ae hinput).mpr (Lp.memLp x)
  let Ψ : ℝ → ℝ≥0∞ := fun θ =>
    ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
      eLpNorm (fun z : Plane => g (z - Real.sqrt θ • w) - g z) 2 (cellMeasure c)
  have hΨg : Tendsto Ψ (𝓝 0) (𝓝 0) := by
    apply tendsto_heatVecGaussianAverage_of_ae_congr hc hfg.symm
    simpa only [f] using tendsto_heatVecGaussianTranslationAverage_zero hc x
  have hbound : ∀ θ, 0 < θ →
      eLpNorm (heatVecL2CLM hc θ x - x) 2 (cellMeasure c) ≤ Ψ θ := by
    intro θ hθ
    have hOut : (heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[cellMeasure c]
        heatVecConvolution θ g := by
      change (heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[cellMeasure c]
        heatVecConvolution θ (fun z => UnforcedLeray.Train.toVec
          (planeRep hc ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
            2 (cellMeasure c) x) z))
      exact heatVecL2CLM_value_ae hc hθ x
    have hdiff : ((heatVecL2CLM hc θ x - x : Lp Vec 2 (cellMeasure c)) : Plane → Vec) =ᵐ[
        cellMeasure c]
        heatVecConvolution θ g - g := by
      filter_upwards [Lp.coeFn_sub (heatVecL2CLM hc θ x) x, hOut, hinput] with z hsub hout hin
      calc
        ((heatVecL2CLM hc θ x - x : Lp Vec 2 (cellMeasure c)) : Plane → Vec) z =
            ((heatVecL2CLM hc θ x : Plane → Vec) z) - ((x : Plane → Vec) z) := hsub
        _ = heatVecConvolution θ g z - g z := by rw [hout, hin]
        _ = (heatVecConvolution θ g - g) z := rfl
    calc
      eLpNorm (heatVecL2CLM hc θ x - x) 2 (cellMeasure c) =
          eLpNorm (heatVecConvolution θ g - g) 2 (cellMeasure c) :=
        eLpNorm_congr_ae hdiff
      _ ≤ ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) *
          eLpNorm (fun z : Plane => g (z - w) - g z) 2 (cellMeasure c) :=
        eLpNorm_heatVecConvolution_sub_le hc hθ hgmeas hgper hgmem
      _ = Ψ θ := by
        dsimp [Ψ]
        exact lintegral_heatKernel2_mul_eq_unit hθ
          (fun w : Plane => eLpNorm (fun z : Plane => g (z - w) - g z)
            2 (cellMeasure c))
  let F : ℝ → ℝ≥0∞ := fun θ => if 0 < θ then
    eLpNorm (heatVecL2CLM hc θ x - x) 2 (cellMeasure c) else 0
  have hF : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hΨg.mono_left nhdsWithin_le_nhds) (fun _ => zero_le) ?_
    intro θ
    by_cases hθ : 0 < θ
    · simpa [F, hθ] using hbound θ hθ
    · simp [F, hθ]
  have hEq : (fun θ : ℝ => eLpNorm (heatVecL2CLM hc θ x - x) 2 (cellMeasure c)) =ᶠ[
      𝓝[>] 0] F := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hpos : 0 < θ := by simpa using hθ
    simp [F, hpos]
  have hLp : Tendsto
      (fun θ : ℝ => eLpNorm (heatVecL2CLM hc θ x - x) 2 (cellMeasure c))
      (𝓝[>] 0) (𝓝 0) := hF.congr' hEq.symm
  have hReal : Tendsto
      (fun θ : ℝ => ENNReal.toReal
        (eLpNorm (heatVecL2CLM hc θ x - x) 2 (cellMeasure c)))
      (𝓝[>] 0) (𝓝 0) := by
    convert (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLp using 1 <;> rfl
  simpa only [Lp.norm_def] using hReal

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_heatVecL2CLM_apply_zero
