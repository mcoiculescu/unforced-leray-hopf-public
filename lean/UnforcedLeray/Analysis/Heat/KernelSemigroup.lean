import UnforcedLeray.Analysis.Heat.KernelNorm
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
# The actual Gaussian convolution law on R³

Completing the square identifies the product of two actual Gaussian kernels
with a translated normalized Gaussian. In particular the convolution integral
is integrable before its value is calculated. The standard viscosity-one
kernel inherits the time-addition law under q=4t.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace UnforcedLeray.Heat.Gaussian

/-- The variance remaining after multiplication of two Gaussian densities. -/
def productVariance (s t : ℝ) : ℝ := s*t/(s+t)

theorem productVariance_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < productVariance s t := div_pos (mul_pos hs ht) (add_pos hs ht)

/-- The normalization factors obey the exact three-dimensional product identity. -/
theorem normalization_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    normalization s * normalization t =
      normalization (s+t) * normalization (productVariance s t) := by
  unfold normalization
  rw [← Real.mul_rpow (mul_pos Real.pi_pos hs).le (mul_pos Real.pi_pos ht).le,
    ← Real.mul_rpow (mul_pos Real.pi_pos (add_pos hs ht)).le
      (mul_pos Real.pi_pos (productVariance_pos hs ht)).le]
  congr 1
  unfold productVariance
  field_simp

/-- Completing the actual Euclidean square with its correct vector center. -/
theorem exponent_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Space) :
    -s⁻¹*‖y‖^2 + -t⁻¹*‖x-y‖^2 =
      -(s+t)⁻¹*‖x‖^2 + -(productVariance s t)⁻¹*‖y-(s/(s+t)) • x‖^2 := by
  simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm y x]
  unfold productVariance
  field_simp
  ring

/-- Literal pointwise product factorization, without any distributional conventions. -/
theorem kernel_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Space) :
    kernel s y * kernel t (x-y) =
      kernel (s+t) x * kernel (productVariance s t) (y-(s/(s+t)) • x) := by
  unfold kernel
  calc
    _ = (normalization s * normalization t) *
        Real.exp (-s⁻¹*‖y‖^2 + -t⁻¹*‖x-y‖^2) := by rw [Real.exp_add]; ring
    _ = (normalization (s+t) * normalization (productVariance s t)) *
        Real.exp (-(s+t)⁻¹*‖x‖^2 + -(productVariance s t)⁻¹*‖y-(s/(s+t)) • x‖^2) := by
      rw [normalization_product hs ht, exponent_product hs ht]
    _ = _ := by rw [Real.exp_add]; ring

/-- The convolution integrand is a genuine L¹ function for every spatial point. -/
theorem kernel_product_integrable {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Space) :
    Integrable (fun y : Space => kernel s y * kernel t (x-y)) := by
  simp_rw [kernel_product hs ht x]
  exact ((kernel_integrable (productVariance_pos hs ht)).comp_sub_right
    ((s/(s+t)) • x)).const_mul _

/-- The normalized Gaussian kernels have the exact convolution semigroup law. -/
theorem integral_kernel_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Space) :
    (∫ y : Space, kernel s y * kernel t (x-y)) = kernel (s+t) x := by
  simp_rw [kernel_product hs ht x]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_kernel (productVariance_pos hs ht),
    mul_one]

end UnforcedLeray.Heat.Gaussian
namespace UnforcedLeray.Heat

/-- Integrability of the actual standard heat-kernel convolution. -/
theorem kernel_product_integrable {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Space) :
    Integrable (fun y : Space => kernel s y * kernel t (x-y)) :=
  Gaussian.kernel_product_integrable (by positivity) (by positivity) x

/-- Exact time-addition law for the viscosity-one heat kernel. -/
theorem integral_kernel_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Space) :
    (∫ y : Space, kernel s y * kernel t (x-y)) = kernel (s+t) x := by
  unfold kernel
  rw [Gaussian.integral_kernel_product (by positivity) (by positivity)]
  congr 1
  ring

end UnforcedLeray.Heat
