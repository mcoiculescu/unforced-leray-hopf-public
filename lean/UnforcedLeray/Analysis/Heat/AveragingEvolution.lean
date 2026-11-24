import UnforcedLeray.Analysis.Heat.Averaging
import UnforcedLeray.Analysis.Heat.DerivativeLp
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Genuine positive-time evolution for L² data

The time derivative is taken under the literal heat integral. An explicit
Gaussian envelope is in L², so Hölder supplies local integrable domination
for every L² input. No continuity, smoothness or uniform bound on the input
is assumed. Identifying this convolution with the spatial Laplacian of the
output is a separate spatial differentiation statement.
-/

noncomputable section
namespace UnforcedLeray.Heat
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal time-derivative convolution converges for L² inputs. -/
theorem average_timeDerivative_integrable {t : ℝ} (ht : 0 < t)
    {f : Space → V} (hf : MemLp f 2 volume) (x : Space) :
    Integrable (fun y : Space => timeDerivativeKernel t y • f (x-y)) := by
  have hs := hf.comp_measurePreserving
    (Measure.measurePreserving_sub_left (volume : Measure Space) x)
  have hm : MemLp (fun y : Space => timeDerivativeKernel t y • f (x-y)) 1 volume :=
    hs.smul (timeDerivativeKernel_memLp_two ht)
  exact memLp_one_iff_integrable.mp hm

/-- Differentiation under the actual Gaussian integral for arbitrary L² input. -/
theorem average_hasDerivAt_timeDerivativeKernel {t : ℝ} (ht : 0 < t)
    {f : Space → V} (hf : MemLp f 2 volume) (x : Space) :
    HasDerivAt (fun s : ℝ => average s f x)
      (∫ y : Space, timeDerivativeKernel t y • f (x-y)) t := by
  let F : ℝ → Space → V := fun s y => kernel s y • f (x-y)
  let F' : ℝ → Space → V := fun s y => timeDerivativeKernel s y • f (x-y)
  let B : Space → ℝ := fun y => (4 * Gaussian.timeEnvelope (4*t) y) * ‖f (x-y)‖
  have hs := hf.comp_measurePreserving
    (Measure.measurePreserving_sub_left (volume : Measure Space) x)
  have hF (s : ℝ) : AEStronglyMeasurable (F s) volume :=
    (Gaussian.kernel_smooth (4*s)).continuous.aestronglyMeasurable.smul hs.aestronglyMeasurable
  have hFd : AEStronglyMeasurable (F' t) volume :=
    ((Gaussian.timeKernel_continuous (4*t)).const_mul 4).aestronglyMeasurable.smul
      hs.aestronglyMeasurable
  have hB : Integrable B := by
    have hm : MemLp B 1 volume :=
      hs.norm.mul ((Gaussian.timeEnvelope_memLp_two (by positivity : 0 < 4*t)).const_mul 4)
    exact memLp_one_iff_integrable.mp hm
  have hbound (y : Space) (s : ℝ) (hs' : s ∈ Ioo (t/2) (2*t)) : ‖F' s y‖ ≤ B y := by
    have he : ‖timeDerivativeKernel s y‖ ≤ 4 * Gaussian.timeEnvelope (4*t) y := by
      have hr := Gaussian.timeKernel_local_bound (t := 4*t) (by positivity) (4*s)
        (show 4*s ∈ Ioo ((4*t)/2) (2*(4*t)) by constructor <;> linarith [hs'.1,hs'.2]) y
      simpa only [timeDerivativeKernel, norm_mul, Real.norm_ofNat] using
        mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ 4 by norm_num)
    exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hdiff (y : Space) (s : ℝ) (hs' : s ∈ Ioo (t/2) (2*t)) :
      HasDerivAt (fun r => F r y) (F' s y) s :=
    (kernel_hasDerivAt_timeDerivativeKernel (by linarith [hs'.1] : 0 < s) y).smul_const
      (f (x-y))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B)
    (Ioo_mem_nhds (by linarith : t/2 < t) (by linarith : t < 2*t))
    (Eventually.of_forall hF) (average_integrable ht hf x) hFd
    (Eventually.of_forall hbound) hB (Eventually.of_forall hdiff)
  exact hd.2

/-- The time derivative is convolution with the actual spatial Laplacian of the kernel. -/
theorem average_hasDerivAt_laplacianKernel {t : ℝ} (ht : 0 < t)
    {f : Space → V} (hf : MemLp f 2 volume) (x : Space) :
    HasDerivAt (fun s : ℝ => average s f x)
      (∫ y : Space, laplacian (kernel t) y • f (x-y)) t := by
  simpa only [timeDerivativeKernel_eq_laplacian ht] using
    average_hasDerivAt_timeDerivativeKernel ht hf x

theorem average_time_continuousOn {f : Space → V} (hf : MemLp f 2 volume) (x : Space) :
    ContinuousOn (fun t : ℝ => average t f x) (Ioi 0) := by
  intro t ht
  exact (average_hasDerivAt_timeDerivativeKernel ht hf x).continuousAt.continuousWithinAt

end UnforcedLeray.Heat
