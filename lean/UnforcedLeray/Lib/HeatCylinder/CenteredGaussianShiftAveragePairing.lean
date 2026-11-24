import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianShiftAverage

/-!
# Scalar pairing formula for the actual Gaussian translation average

The centered Bochner average pairs against every centered `L²` field as the Gaussian integral of
its translation pairings. This is the Fubini-side interface for comparison with literal heat.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (heatKernel2)

/-- Pairing the actual Bochner translation average against an arbitrary centered `L²` field is
the Gaussian average of the actual translated pairings. -/
theorem inner_centeredGaussianShiftAverageCLM {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (x y : L2v c) :
    inner ℝ (centeredGaussianShiftAverageCLM hc hθ x) y =
      ∫ w : Plane, heatKernel2 θ w * inner ℝ (planeShiftL2CLM hc w x) y := by
  rw [centeredGaussianShiftAverageCLM_apply, centeredGaussianShiftAverage]
  have hint := integrable_heatKernel2_smul_planeShiftL2CLM hc hθ x
  calc
    inner ℝ (∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x) y =
        inner ℝ y (∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x) :=
      real_inner_comm _ _
    _ = ∫ w : Plane, inner ℝ y (heatKernel2 θ w • planeShiftL2CLM hc w x) :=
      (integral_inner hint y).symm
    _ = ∫ w : Plane, heatKernel2 θ w * inner ℝ (planeShiftL2CLM hc w x) y := by
      refine integral_congr_ae ?_
      filter_upwards [] with w
      simp [real_inner_smul_right, real_inner_comm]

#print axioms UnforcedLeray.HeatCylinder.inner_centeredGaussianShiftAverageCLM

end UnforcedLeray.HeatCylinder
