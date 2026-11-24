import UnforcedLeray.Analysis.Heat.Derivatives
import UnforcedLeray.Analysis.Heat.KernelNorm

/-!
# Explicit scale bounds for the standard R³ heat derivative kernels

The constants below are fixed positive real numbers. The powers of time come
from the actual Gaussian kernel estimates and the viscosity-one parameter 4t.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat

/-- A fixed constant in the first derivative smoothing estimate. -/
def firstSmoothingConstant : ℝ := 2 * Real.sqrt 2 * (2 : ℝ) ^ ((3 : ℝ) / 2)

/-- A fixed constant in the second derivative smoothing estimate. -/
def secondSmoothingConstant : ℝ := 10 * (2 : ℝ) ^ ((3 : ℝ) / 2)

theorem firstSmoothingConstant_pos : 0 < firstSmoothingConstant := by
  unfold firstSmoothingConstant
  positivity

theorem secondSmoothingConstant_pos : 0 < secondSmoothingConstant := by
  unfold secondSmoothingConstant
  positivity

@[simp] theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

/-- The actual normalized first derivative kernel has C t^(-1/2) finite mass. -/
theorem firstDerivativeKernel_L1_scale_bound {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    (∫ x : Space, ‖Gaussian.firstKernel (4*t) (coordinateVector i) x‖) ≤
      firstSmoothingConstant * t ^ (-(1 : ℝ) / 2) := by
  have h := Gaussian.firstKernel_L1_bound (t := 4*t) (by positivity) (coordinateVector i)
  simp only [norm_coordinateVector, mul_one] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num))
    firstSmoothingConstant_pos.le

/-- The actual normalized ordered-second kernel has C t⁻¹ finite mass. -/
theorem secondDerivativeKernel_L1_scale_bound {t : ℝ} (ht : 0 < t) (i j : Fin 3) :
    (∫ x : Space, ‖Gaussian.secondKernel (4*t) (coordinateVector i) (coordinateVector j) x‖) ≤
      secondSmoothingConstant * t⁻¹ := by
  have h := Gaussian.secondKernel_L1_bound (t := 4*t) (by positivity)
    (coordinateVector i) (coordinateVector j)
  simp only [norm_coordinateVector, mul_one] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left (inv_anti₀ ht (by linarith))
    secondSmoothingConstant_pos.le

end UnforcedLeray.Heat
