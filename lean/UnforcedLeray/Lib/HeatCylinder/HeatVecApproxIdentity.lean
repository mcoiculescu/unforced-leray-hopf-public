import UnforcedLeray.Lib.HeatCylinder.HeatVecActualContraction

/-!
# Translation average estimate for the actual vector heat increment

The heat increment is the Gaussian average of translated increments. Minkowski then reduces its
normalized-cell L² continuity at age zero to continuity of periodic translations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)

private theorem ae_integrable_heatVecConvolution_integrand {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) {f : Plane → Vec} (hf : AEStronglyMeasurable f volume)
    (hper : IsQPeriodic c f) (hmem : MemLp f 2 (cellMeasure c)) :
    ∀ᵐ z ∂(cellMeasure c),
      Integrable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) := by
  let k : Plane → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w)
  have hk : Measurable k := ENNReal.measurable_ofReal.comp
    (UnforcedLeray.B0284.measurable_heatKernel2_right θ)
  have hk' : ∀ w, k w ≠ ⊤ := fun w => ENNReal.ofReal_ne_top
  have hmass : ∫⁻ w : Plane, k w = 1 := by
    dsimp [k]
    exact UnforcedLeray.B0284.lintegral_heatKernel2 hθ
  have hfinite := UnforcedLeray.B0296.ae_kernelAbs_lt_top' hc hk hk'
    (by rw [hmass]; exact ENNReal.one_ne_top) hper hf
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  filter_upwards [hfinite] with z hz
  have hdom : ∀ (w : Plane) (x : Vec),
      ‖UnforcedLeray.B0284.heatKernel2 θ w • x‖ₑ ≤ k w * ‖x‖ₑ := by
    intro w x
    rw [enorm_smul, Real.enorm_of_nonneg
      (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
  have hmeas : AEStronglyMeasurable
      (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)) volume :=
    (UnforcedLeray.B0284.measurable_heatKernel2_right θ).aestronglyMeasurable.smul
      (UnforcedLeray.B0296.aestronglyMeasurable_comp_sub_left hf z)
  refine ⟨hmeas, ?_⟩
  exact (lintegral_mono fun w => hdom w (f (z - w))).trans_lt hz

/-- For a periodic vector field in normalized-cell L², the actual Gaussian heat increment is
bounded by the Gaussian average of its translation increments. -/
theorem eLpNorm_heatVecConvolution_sub_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f : Plane → Vec} (hf : AEStronglyMeasurable f volume)
    (hper : IsQPeriodic c f) (hmem : MemLp f 2 (cellMeasure c)) :
    eLpNorm (heatVecConvolution θ f - f) 2 (cellMeasure c) ≤
      ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) *
        eLpNorm (fun z : Plane => f (z - w) - f z) 2 (cellMeasure c) := by
  let k : Plane → ℝ := UnforcedLeray.B0284.heatKernel2 θ
  have hmass : ∫ w : Plane, k w = 1 := by
    dsimp [k]
    exact UnforcedLeray.B0284.integral_heatKernel2 hθ
  have hInt := ae_integrable_heatVecConvolution_integrand hc hθ hf hper hmem
  have hrep : heatVecConvolution θ f - f =ᵐ[cellMeasure c]
      fun z => ∫ w : Plane, k w • (f (z - w) - f z) := by
    filter_upwards [hInt] with z hz
    have hconst : Integrable (fun w : Plane => k w • f z) :=
      (UnforcedLeray.B0284.integrable_heatKernel2 hθ).smul_const (f z)
    calc
      heatVecConvolution θ f z - f z =
          (∫ w : Plane, k w • f (z - w)) - ∫ w : Plane, k w • f z := by
        rw [heatVecConvolution]
        rw [integral_smul_const, hmass, one_smul]
      _ = ∫ w : Plane, k w • (f (z - w) - f z) := by
        rw [← integral_sub hz hconst]
        congr 1
        funext w
        rw [smul_sub]
  rw [eLpNorm_congr_ae hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun z w : Plane => k w • (f (z - w) - f z))
      ((cellMeasure c).prod volume) := by
    have hshift : AEStronglyMeasurable (Function.uncurry fun z w : Plane => f (z - w))
        ((cellMeasure c).prod volume) :=
      (UnforcedLeray.B0296.aestronglyMeasurable_comp_sub hf).mono_ac
        ((UnforcedLeray.B0284.cellMeasure_ac c).prod Measure.AbsolutelyContinuous.rfl)
    have hleft : AEStronglyMeasurable (Function.uncurry fun z w : Plane => f z)
        ((cellMeasure c).prod volume) := by
      exact (hf.mono_ac (UnforcedLeray.B0284.cellMeasure_ac c)).comp_fst
    exact ((UnforcedLeray.B0284.measurable_heatKernel2_right θ).comp measurable_snd)
      |>.aestronglyMeasurable.smul (hshift.sub hleft)
  calc
    eLpNorm (fun z => ∫ w : Plane, k w • (f (z - w) - f z)) 2 (cellMeasure c) ≤
        ∫⁻ w : Plane, eLpNorm (fun z : Plane => k w • (f (z - w) - f z)) 2
          (cellMeasure c) :=
      NonUniqueEuler.Conv.eLpNorm_integral_le hjoint
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    _ = ∫⁻ w : Plane, ENNReal.ofReal (k w) *
          eLpNorm (fun z : Plane => f (z - w) - f z) 2 (cellMeasure c) := by
      refine lintegral_congr fun w => ?_
      change eLpNorm (k w • fun z : Plane => f (z - w) - f z) 2 (cellMeasure c) = _
      rw [eLpNorm_const_smul]
      rw [Real.enorm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_heatVecConvolution_sub_le
