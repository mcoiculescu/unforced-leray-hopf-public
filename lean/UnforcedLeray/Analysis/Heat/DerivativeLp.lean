import UnforcedLeray.Analysis.Heat.KernelEvolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# L² Gaussian derivative kernels

All derivatives and the local time envelope below are the concrete Gaussian
functions. Their L² membership supplies Hölder domination for actual L² data.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace UnforcedLeray.Heat.Gaussian

/-- Gaussian decay gives a genuine finite square integral for any positive exponent. -/
theorem exp_memLp_two {b : ℝ} (hb : 0 < b) :
    MemLp (fun x : Space => Real.exp (-b * ‖x‖^2)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).aestronglyMeasurable)).mpr
  have he : (fun x : Space => Real.exp (-b * ‖x‖^2)^2) =
      (fun x : Space => Real.exp (-(2*b) * ‖x‖^2)) := by
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change Integrable (fun x : Space => Real.exp (-b * ‖x‖^2)^2)
  rw [he]
  exact exp_integrable (by positivity)

theorem wideKernel_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (wideKernel t) 2 volume :=
  (exp_memLp_two (inv_pos.mpr (by positivity : 0 < 2*t))).const_mul _

theorem firstKernel_memLp_two {t : ℝ} (ht : 0 < t) (a : Space) :
    MemLp (firstKernel t a) 2 volume := by
  apply ((wideKernel_memLp_two ht).const_mul (2*t⁻¹*(1+2*t)*‖a‖)).mono'
    (firstKernel_smooth t a).continuous.aestronglyMeasurable
  exact Eventually.of_forall (firstKernel_bound ht a)

theorem secondKernel_memLp_two {t : ℝ} (ht : 0 < t) (a b : Space) :
    MemLp (secondKernel t a b) 2 volume := by
  apply ((wideKernel_memLp_two ht).const_mul (10*t⁻¹*‖a‖*‖b‖)).mono'
    (secondKernel_smooth t a b).continuous.aestronglyMeasurable
  exact Eventually.of_forall (secondKernel_bound ht a b)

theorem timeKernel_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (timeKernel t) 2 volume := by
  apply ((wideKernel_memLp_two ht).const_mul ((15/2:ℝ)*t⁻¹)).mono'
    (timeKernel_continuous t).aestronglyMeasurable
  exact Eventually.of_forall (timeKernel_bound ht)

theorem timeEnvelope_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (timeEnvelope t) 2 volume :=
  (exp_memLp_two (inv_pos.mpr (by positivity : 0 < 4*t))).const_mul _

end UnforcedLeray.Heat.Gaussian

namespace UnforcedLeray.Heat
/-- The explicit time derivative of the standard viscosity-one heat kernel. -/
def timeDerivativeKernel (t : ℝ) (x : Space) : ℝ :=
  4 * Gaussian.timeKernel (4*t) x

theorem kernel_hasDerivAt_timeDerivativeKernel {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s : ℝ => kernel s x) (timeDerivativeKernel t x) t := by
  have h := (Gaussian.kernel_hasDerivAt (t := 4*t) (by positivity) x).comp t
    ((hasDerivAt_id t).const_mul 4)
  apply h.congr_deriv
  change Gaussian.timeKernel (4*t) x * (4*1) = 4 * Gaussian.timeKernel (4*t) x
  ring

theorem timeDerivativeKernel_eq_laplacian {t : ℝ} (ht : 0 < t) (x : Space) :
    timeDerivativeKernel t x = laplacian (kernel t) x :=
  (kernel_hasDerivAt_timeDerivativeKernel ht x).unique (kernel_hasDerivAt_laplacian ht x)

theorem timeDerivativeKernel_memLp_two {t : ℝ} (ht : 0 < t) :
    MemLp (timeDerivativeKernel t) 2 volume :=
  (Gaussian.timeKernel_memLp_two (by positivity : 0 < 4*t)).const_mul 4

end UnforcedLeray.Heat
