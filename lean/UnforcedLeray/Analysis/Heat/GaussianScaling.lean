import UnforcedLeray.Analysis.Heat.GaussianOrbit
import UnforcedLeray.Analysis.Heat.KernelNorm
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The actual three-dimensional Gaussian change of variables in L²-valued integrals. -/
noncomputable section
open MeasureTheory
namespace UnforcedLeray.Heat.Gaussian

theorem kernel_squareScale {r : ℝ} (hr : 0 < r) (y : Space) :
    kernel (r ^ 2) (r • y) = (r ^ 3)⁻¹ * kernel 1 y := by
  have hn : normalization (r ^ 2) = (r ^ 3)⁻¹ * normalization 1 := by
    rw [normalization, normalization, mul_one,
      Real.mul_rpow Real.pi_pos.le (sq_nonneg r),
      ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num [Real.rpow_neg hr.le]
    ring
  have he : -(r ^ 2)⁻¹ * ‖r • y‖ ^ 2 = -‖y‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, mul_pow]
    field_simp
  rw [kernel, hn, he, kernel]
  norm_num
  ring

end UnforcedLeray.Heat.Gaussian

namespace UnforcedLeray.Heat
/-- The Gaussian translation integral equals the literal scaled-kernel translation integral. -/
theorem orbitAverage_eq_scaledKernel {r : ℝ} (hr : 0 < r) (u : L2Space) :
    orbitAverage r u = ∫ x : Space, Gaussian.kernel (r ^ 2) x • translation x u := by
  let F : Space → L2Space := fun x => Gaussian.kernel (r ^ 2) x • translation x u
  have hJac := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) F r (hR := hr.le)
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd] at hJac
  have he : (fun y : Space => F (r • y)) =
      fun y : Space => (r ^ 3)⁻¹ • (Gaussian.kernel 1 y • translation (r • y) u) := by
    funext y
    dsimp only [F]
    rw [Gaussian.kernel_squareScale hr, mul_smul]
  rw [he, integral_smul] at hJac
  have hc := congrArg (fun v : L2Space => r ^ 3 • v) hJac
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero _ hr.ne'
  simpa only [smul_smul, mul_inv_cancel₀ hr3, one_smul, orbitAverage] using hc

/-- The normalized orbit with radius sqrt(4t) has precisely the standard heat kernel. -/
theorem orbitAverage_eq_heatKernel {t : ℝ} (ht : 0 < t) (u : L2Space) :
    orbitAverage (Real.sqrt (4*t)) u = ∫ x : Space, kernel t x • translation x u := by
  rw [orbitAverage_eq_scaledKernel (Real.sqrt_pos.mpr (by positivity : 0 < 4*t))]
  rw [Real.sq_sqrt (by positivity : 0 ≤ 4*t)]
  rfl

end UnforcedLeray.Heat
