import UnforcedLeray.Analysis.Heat.Kernel

/-! Exact L² mass of the literal Gaussian, and viscosity-one normalization. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace UnforcedLeray.Heat.Gaussian

theorem eLpNorm_two_toReal_eq_sqrt {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] {μ : Measure α} {f : α → V} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [toReal_eLpNorm hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hf.aestronglyMeasurable]
  norm_num [Real.sqrt_eq_rpow, Real.rpow_two]

/-- The exact finite L² mass, with the correct three-dimensional factor. -/
theorem integral_kernel_sq {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, kernel t x ^ 2) = (2 * Real.pi * t) ^ (-(3 : ℝ) / 2) := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  have he : (fun x : Space => kernel t x ^ 2) =
      (fun x : Space => normalization t ^ 2 * Real.exp (-(2 * t⁻¹) * ‖x‖ ^ 2)) := by
    funext x
    rw [kernel, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he, integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < 2 * t⁻¹), hdim]
  norm_num only [Nat.cast_ofNat]
  have hq : Real.pi / (2 * t⁻¹) = (Real.pi * t) / 2 := by field_simp
  rw [hq, normalization, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (mul_pos Real.pi_pos ht).le,
    Real.div_rpow (mul_pos Real.pi_pos ht).le (by norm_num : (0 : ℝ) ≤ 2)]
  have halg : ∀ a b c : ℝ, a * (b / c) = (a * b) * c⁻¹ := by intros; ring
  rw [halg, ← Real.rpow_add (mul_pos Real.pi_pos ht),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hb : 2 * Real.pi * t = 2 * (Real.pi * t) := by ring
  rw [hb, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (mul_pos Real.pi_pos ht).le]
  norm_num
  ring

/-- Exact real-valued L² norm of the actual integrable kernel. -/
theorem eLpNorm_kernel_toReal {t : ℝ} (ht : 0 < t) :
    (eLpNorm (kernel t) 2 volume).toReal = (2 * Real.pi * t) ^ (-(3 : ℝ) / 4) := by
  rw [eLpNorm_two_toReal_eq_sqrt (kernel_memLp ht)]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [integral_kernel_sq ht, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity : 0 ≤ 2 * Real.pi * t)]
  norm_num

end UnforcedLeray.Heat.Gaussian

namespace UnforcedLeray.Heat
/-- The standard viscosity-one heat kernel on R³. -/
def kernel (t : ℝ) : Space → ℝ := Gaussian.kernel (4 * t)

theorem kernel_formula (t : ℝ) (x : Space) :
    kernel t x = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) := by
  simp only [kernel, Gaussian.kernel, Gaussian.normalization]
  congr 2
  ring

theorem kernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (kernel t) :=
  Gaussian.kernel_integrable (by positivity)

theorem integral_kernel {t : ℝ} (ht : 0 < t) : (∫ x : Space, kernel t x) = 1 :=
  Gaussian.integral_kernel (by positivity)

theorem kernel_nonneg {t : ℝ} (ht : 0 < t) (x : Space) : 0 ≤ kernel t x :=
  Gaussian.kernel_nonneg (by positivity) x

theorem kernel_memLp_two {t : ℝ} (ht : 0 < t) : MemLp (kernel t) 2 volume :=
  Gaussian.kernel_memLp (by positivity)

theorem eLpNorm_kernel_toReal {t : ℝ} (ht : 0 < t) :
    (eLpNorm (kernel t) 2 volume).toReal = (8 * Real.pi * t) ^ (-(3 : ℝ) / 4) := by
  rw [kernel, Gaussian.eLpNorm_kernel_toReal (by positivity)]
  congr 1
  ring

end UnforcedLeray.Heat
