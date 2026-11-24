import UnforcedLeray.Analysis.Heat.DerivativeLp

/-! Integrable time-derivative kernels and their actual C/t L¹ bound. -/

noncomputable section
open MeasureTheory Filter
namespace UnforcedLeray.Heat

theorem timeDerivativeKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (timeDerivativeKernel t) :=
  (Gaussian.timeKernel_integrable (by positivity : 0 < 4*t)).const_mul 4

/-- Positive-time differentiation has the usual inverse-time Gaussian majorant. -/
theorem timeDerivativeKernel_bound {t : ℝ} (ht : 0 < t) (x : Space) :
    ‖timeDerivativeKernel t x‖ ≤ ((15/2:ℝ)*t⁻¹) * Gaussian.wideKernel (4*t) x := by
  have hc : 4 * ((15/2:ℝ) * (4*t)⁻¹) = (15/2:ℝ) * t⁻¹ := by field_simp
  calc
    _ = 4 * ‖Gaussian.timeKernel (4*t) x‖ := by
      simp only [timeDerivativeKernel, norm_mul, Real.norm_ofNat]
    _ ≤ 4 * (((15/2:ℝ)*(4*t)⁻¹) * Gaussian.wideKernel (4*t) x) :=
      mul_le_mul_of_nonneg_left (Gaussian.timeKernel_bound (by positivity) x) (by norm_num)
    _ = _ := by rw [← mul_assoc, hc]

/-- The literal derivative density has an L¹ norm bounded by a fixed constant over t. -/
theorem timeDerivativeKernel_L1_bound {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, ‖timeDerivativeKernel t x‖) ≤
      ((15/2:ℝ) * (2:ℝ)^((3:ℝ)/2)) * t⁻¹ := by
  calc
    _ ≤ ∫ x : Space, ((15/2:ℝ)*t⁻¹) * Gaussian.wideKernel (4*t) x :=
      integral_mono (timeDerivativeKernel_integrable ht).norm
        ((Gaussian.wideKernel_integrable (by positivity : 0 < 4*t)).const_mul _)
        (timeDerivativeKernel_bound ht)
    _ = _ := by
      rw [integral_const_mul, Gaussian.integral_wideKernel (by positivity : 0 < 4*t)]
      ring

theorem laplacian_kernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (laplacian (kernel t)) :=
  (timeDerivativeKernel_integrable ht).congr
    (Eventually.of_forall (timeDerivativeKernel_eq_laplacian ht))

theorem laplacian_kernel_L1_bound {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, ‖laplacian (kernel t) x‖) ≤
      ((15/2:ℝ) * (2:ℝ)^((3:ℝ)/2)) * t⁻¹ := by
  simpa only [timeDerivativeKernel_eq_laplacian ht] using timeDerivativeKernel_L1_bound ht

end UnforcedLeray.Heat
