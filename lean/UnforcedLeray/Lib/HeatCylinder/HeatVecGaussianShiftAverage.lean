import UnforcedLeray.Lib.HeatCylinder.HeatVecPlaneShiftOrbit
import UnforcedLeray.Units.B0284.Defs

/-!
# The actual Gaussian average of cylinder translations

At each positive age, the Gaussian-weighted translation orbit defines a contractive continuous
linear map on the centered cylinder `L²` quotient. The remaining identification with the literal
B0284 heat convolution is proved separately.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (heatKernel2)

/-- The vector-valued Bochner integral of actual planar translations against the actual Gaussian
kernel. -/
noncomputable def centeredGaussianShiftAverage {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : L2v c) : L2v c :=
  ∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x

theorem centeredGaussianShiftAverage_add {c θ : ℝ} (hc : 0 < c) (_hθ : 0 < θ)
    (x y : L2v c) :
    centeredGaussianShiftAverage hc _hθ (x + y) =
      centeredGaussianShiftAverage hc _hθ x + centeredGaussianShiftAverage hc _hθ y := by
  change (∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w (x + y)) = _
  have hpoint : (fun w : Plane => heatKernel2 θ w • planeShiftL2CLM hc w (x + y)) =
      fun w => (heatKernel2 θ w • planeShiftL2CLM hc w x) +
        (heatKernel2 θ w • planeShiftL2CLM hc w y) := by
    funext w
    rw [map_add, smul_add]
  rw [hpoint, integral_add
    (integrable_heatKernel2_smul_planeShiftL2CLM hc _hθ x)
    (integrable_heatKernel2_smul_planeShiftL2CLM hc _hθ y)]
  rfl

theorem centeredGaussianShiftAverage_smul {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (r : ℝ) (x : L2v c) :
    centeredGaussianShiftAverage hc hθ (r • x) =
      r • centeredGaussianShiftAverage hc hθ x := by
  rw [centeredGaussianShiftAverage, centeredGaussianShiftAverage]
  have hpoint : (fun w : Plane => heatKernel2 θ w •
      planeShiftL2CLM hc w (r • x)) =
      fun w => r • (heatKernel2 θ w • planeShiftL2CLM hc w x) := by
    funext w
    rw [map_smul]
    module
  rw [hpoint, integral_smul]

/-- Contractivity of the actual Gaussian translation average follows from unit kernel mass and
isometry of each centered-cell translation. -/
theorem norm_centeredGaussianShiftAverage_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : L2v c) :
    ‖centeredGaussianShiftAverage hc hθ x‖ ≤ ‖x‖ := by
  rw [centeredGaussianShiftAverage]
  calc
    ‖∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x‖ ≤
        ∫ w : Plane, ‖heatKernel2 θ w • planeShiftL2CLM hc w x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ w : Plane, heatKernel2 θ w * ‖x‖ := by
      congr 1
      funext w
      rw [norm_smul,
        Real.norm_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
      change _ * ‖UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)
        (UnforcedLeray.TrainB.etaShiftL2 _ _ x)‖ = _
      rw [(UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).norm_map,
        (UnforcedLeray.TrainB.etaShiftL2 _ _).norm_map]
    _ = (∫ w : Plane, heatKernel2 θ w) * ‖x‖ := by
      rw [integral_mul_const]
    _ = ‖x‖ := by rw [UnforcedLeray.B0284.integral_heatKernel2 hθ, one_mul]

/-- The Gaussian translation average as a genuine continuous linear operator. -/
noncomputable def centeredGaussianShiftAverageCLM {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) : L2v c →L[ℝ] L2v c :=
  ({ toFun := centeredGaussianShiftAverage hc hθ
     map_add' := centeredGaussianShiftAverage_add hc hθ
     map_smul' := centeredGaussianShiftAverage_smul hc hθ } : L2v c →ₗ[ℝ] L2v c).mkContinuous 1
    (by
      intro x
      change ‖centeredGaussianShiftAverage hc hθ x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_centeredGaussianShiftAverage_le hc hθ x)

@[simp] theorem centeredGaussianShiftAverageCLM_apply {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (x : L2v c) :
    centeredGaussianShiftAverageCLM hc hθ x = centeredGaussianShiftAverage hc hθ x := rfl

#print axioms UnforcedLeray.HeatCylinder.centeredGaussianShiftAverage_add
#print axioms UnforcedLeray.HeatCylinder.centeredGaussianShiftAverage_smul
#print axioms UnforcedLeray.HeatCylinder.norm_centeredGaussianShiftAverage_le
#print axioms UnforcedLeray.HeatCylinder.centeredGaussianShiftAverageCLM

end UnforcedLeray.HeatCylinder
