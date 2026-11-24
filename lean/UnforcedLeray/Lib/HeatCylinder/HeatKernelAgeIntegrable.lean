import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative
import UnforcedLeray.Units.B0296.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integrability of the actual Gaussian heat-age derivative

The age derivative has only a quadratic polynomial factor beyond the planar Gaussian. This leaf
proves its actual plane integrability from the pinned one-dimensional Gaussian moment bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0191 (heatKernel)
open UnforcedLeray.B0284 (heatKernel2)

/-- A coordinate-square weighted one-dimensional heat kernel is integrable. -/
theorem integrable_sq_mul_heatKernel1 {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun x : ℝ => x ^ 2 * heatKernel 1 θ x) := by
  let b : ℝ := (4 * θ)⁻¹
  have hb : 0 < b := by positivity
  have hbase := integrable_rpow_mul_exp_neg_mul_sq (b := b) (s := 2) hb (by norm_num)
  have hpow : (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-b * x ^ 2)) =
      fun x => x ^ 2 * Real.exp (-b * x ^ 2) := by
    funext x
    exact congrArg (fun q : ℝ => q * Real.exp (-b * x ^ 2)) (Real.rpow_natCast x 2)
  rw [hpow] at hbase
  have hbase' : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := hbase
  have hpref : 0 ≤ (Real.sqrt (4 * Real.pi * θ))⁻¹ := by positivity
  have hmul : Integrable (fun x : ℝ =>
      (Real.sqrt (4 * Real.pi * θ))⁻¹ * (x ^ 2 * Real.exp (-b * x ^ 2))) :=
    hbase'.const_mul _
  have heq : (fun x : ℝ => x ^ 2 * heatKernel 1 θ x) =
      fun x => (Real.sqrt (4 * Real.pi * θ))⁻¹ * (x ^ 2 * Real.exp (-b * x ^ 2)) := by
    funext x
    simp [heatKernel, b]
    ring
  rw [heq]
  exact hmul

/-- The actual age derivative of B0284's planar Gaussian is integrable for every positive age. -/
theorem integrable_heatKernel2AgeDerivative {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : Plane => heatKernel2AgeDerivative θ w) := by
  have h0 : Integrable (heatKernel 1 θ) := UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have h2 : Integrable (fun x : ℝ => x ^ 2 * heatKernel 1 θ x) :=
    integrable_sq_mul_heatKernel1 hθ
  have h00 := h0.mul_prod h0
  have h20 := h2.mul_prod h0
  have h02 := h0.mul_prod h2
  have hsum : Integrable (fun w : Plane =>
      ((w.1 ^ 2 * heatKernel 1 θ w.1) * heatKernel 1 θ w.2) / (4 * θ ^ 2) +
      (heatKernel 1 θ w.1 * (w.2 ^ 2 * heatKernel 1 θ w.2)) / (4 * θ ^ 2) -
      (heatKernel 1 θ w.1 * heatKernel 1 θ w.2) / θ) (volume.prod volume) := by
    have h' := (h20.div_const (4 * θ ^ 2)).add
      ((h02.div_const (4 * θ ^ 2)).sub (h00.div_const θ))
    refine h'.congr (ae_of_all _ fun w => ?_)
    simp only [Pi.add_apply, Pi.sub_apply] <;> ring
  have hEq : (fun w : Plane => heatKernel2AgeDerivative θ w) = fun w =>
      ((w.1 ^ 2 * heatKernel 1 θ w.1) * heatKernel 1 θ w.2) / (4 * θ ^ 2) +
      (heatKernel 1 θ w.1 * (w.2 ^ 2 * heatKernel 1 θ w.2)) / (4 * θ ^ 2) -
      (heatKernel 1 θ w.1 * heatKernel 1 θ w.2) / θ := by
    funext w
    simp [heatKernel2AgeDerivative, heatKernel2]
    ring
  rw [hEq, Measure.volume_eq_prod]
  exact hsum

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.integrable_sq_mul_heatKernel1
#print axioms UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative
