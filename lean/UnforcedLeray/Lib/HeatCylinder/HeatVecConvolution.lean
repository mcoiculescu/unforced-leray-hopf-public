import UnforcedLeray.Lib.HeatCylinder.HeatVecL2Semigroup
import UnforcedLeray.Units.B0296.Conv

/-!
# Euclidean-vector Gaussian convolution estimates on the normalized cylinder

This leaf records the contractive estimate directly in the Hilbert vector norm. It uses the
positive scalar Gaussian kernel and the generic normed-value kernel Minkowski bound, avoiding the
loss from the max-norm Plane coordinate bridge.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)

/-- The literal positive-age Gaussian convolution of a periodic Euclidean-vector field. -/
def heatVecConvolution (θ : ℝ) (f : Plane → Vec) (z : Plane) : Vec :=
  ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)

/-- Actual Gaussian vector convolution is contractive in normalized-cell `L²` for periodic
fields. The estimate is the generic scalar-kernel Minkowski inequality with kernel mass one. -/
theorem eLpNorm_heatVecConvolution_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {f : Plane → Vec} (hper : IsQPeriodic c f) (hf : AEStronglyMeasurable f volume)
    (hp : 1 ≤ (2 : ℝ≥0∞)) (hp' : (2 : ℝ≥0∞) ≠ ⊤) :
    eLpNorm (heatVecConvolution θ f) 2 (cellMeasure c) ≤ eLpNorm f 2 (cellMeasure c) := by
  let k : Plane → ℝ≥0∞ := fun w => ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w)
  have hk : Measurable k := by
    exact ENNReal.measurable_ofReal.comp
      (UnforcedLeray.B0284.measurable_heatKernel2_right θ)
  have hk' : ∀ w, k w ≠ ⊤ := fun w => ENNReal.ofReal_ne_top
  have hKernel := UnforcedLeray.B0296.eLpNorm_kernelAbs_le' (E := Vec) hc hk hk'
    hper hf hp hp'
  have hMass : ∫⁻ w : Plane, k w = 1 := by
    dsimp [k]
    exact UnforcedLeray.B0284.lintegral_heatKernel2 hθ
  calc
    eLpNorm (heatVecConvolution θ f) 2 (cellMeasure c) ≤
        eLpNorm (fun z => ∫⁻ w : Plane, k w * ‖f (z - w)‖ₑ) 2 (cellMeasure c) := by
      apply eLpNorm_mono_enorm
      intro z
      calc
        ‖heatVecConvolution θ f z‖ₑ ≤
            ∫⁻ w : Plane, ‖UnforcedLeray.B0284.heatKernel2 θ w • f (z - w)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ w : Plane, k w * ‖f (z - w)‖ₑ := by
          refine lintegral_congr fun w => ?_
          rw [enorm_smul,
            Real.enorm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
    _ ≤ (∫⁻ w : Plane, k w) * eLpNorm f 2 (cellMeasure c) := hKernel
    _ = eLpNorm f 2 (cellMeasure c) := by rw [hMass, one_mul]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_heatVecConvolution_le
