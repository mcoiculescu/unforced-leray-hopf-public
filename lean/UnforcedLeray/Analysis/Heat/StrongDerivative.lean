import UnforcedLeray.Analysis.Heat.StrongDerivativeSum
import UnforcedLeray.Analysis.Heat.IntegrationByParts
import UnforcedLeray.Analysis.Heat.StrongContinuity
import UnforcedLeray.Analysis.Heat.SobolevContinuity
import UnforcedLeray.Analysis.Heat.TimeBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Strong L² differentiation of the actual heat semigroup

The proof differentiates the genuine Hilbert-valued Bochner integral of
translations. The explicit Gaussian local time envelope is integrable and
the translation orbit has constant L² norm. Thus domination holds in the
strong L² norm for every L² datum, without any datum Sobolev hypothesis.
-/

noncomputable section
namespace UnforcedLeray.Heat
open MeasureTheory Filter Set
open scoped Topology

/-- Positive-time strong L² differentiation with the actual time-derivative kernel. -/
theorem heatOperator_hasDerivAt_convolution {t : ℝ} (ht : 0 < t) (u : L2Space) :
    HasDerivAt (fun s : ℝ => heatOperator s u)
      (convolutionOperator (timeDerivativeKernel t) (timeDerivativeKernel_integrable ht) u) t := by
  let F : ℝ → Space → L2Space := fun s y => kernel s y • translation y u
  let F' : ℝ → Space → L2Space := fun s y => timeDerivativeKernel s y • translation y u
  let B : Space → ℝ := fun y => (4 * Gaussian.timeEnvelope (4*t) y) * ‖u‖
  have hF (s : ℝ) : AEStronglyMeasurable (F s) volume :=
    (Gaussian.kernel_smooth (4*s)).continuous.aestronglyMeasurable.smul
      (translation_continuous u).aestronglyMeasurable
  have hFd : AEStronglyMeasurable (F' t) volume :=
    ((Gaussian.timeKernel_continuous (4*t)).const_mul 4).aestronglyMeasurable.smul
      (translation_continuous u).aestronglyMeasurable
  have hB : Integrable B :=
    ((Gaussian.timeEnvelope_integrable (by positivity : 0 < 4*t)).const_mul 4).mul_const ‖u‖
  have hbound (y : Space) (s : ℝ) (hs : s ∈ Ioo (t/2) (2*t)) : ‖F' s y‖ ≤ B y := by
    have he : ‖timeDerivativeKernel s y‖ ≤ 4 * Gaussian.timeEnvelope (4*t) y := by
      have hr := Gaussian.timeKernel_local_bound (t := 4*t) (by positivity) (4*s)
        (show 4*s ∈ Ioo ((4*t)/2) (2*(4*t)) by constructor <;> linarith [hs.1,hs.2]) y
      simpa only [timeDerivativeKernel, norm_mul, Real.norm_ofNat] using
        mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ 4 by norm_num)
    change ‖timeDerivativeKernel s y • translation y u‖ ≤ _
    rw [norm_smul, norm_translation]
    exact mul_le_mul_of_nonneg_right he (norm_nonneg u)
  have hdiff (y : Space) (s : ℝ) (hs : s ∈ Ioo (t/2) (2*t)) :
      HasDerivAt (fun r => F r y) (F' s y) s :=
    (kernel_hasDerivAt_timeDerivativeKernel (by linarith [hs.1] : 0 < s) y).smul_const
      (translation y u)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := B)
    (Ioo_mem_nhds (by linarith : t/2 < t) (by linarith : t < 2*t))
    (Eventually.of_forall hF)
    (convolutionOrbit_integrable (kernel t) (kernel_integrable ht) u) hFd
    (Eventually.of_forall hbound) hB (Eventually.of_forall hdiff)
  have heq : (fun s : ℝ => heatOperator s u) =ᶠ[𝓝 t]
      (fun s : ℝ => ∫ y : Space, F s y) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [heatOperator_pos hs, convolutionOperator_eq_integral_translationOrbit]
  have hresult := hd.2.congr_of_eventuallyEq heq
  simpa only [F', ← convolutionOperator_eq_integral_translationOrbit
    (timeDerivativeKernel t) (timeDerivativeKernel_integrable ht) u] using hresult

/-- Strong differentiation is genuine L² differentiability at every positive time. -/
theorem heatOperator_differentiableAt {t : ℝ} (ht : 0 < t) (u : L2Space) :
    DifferentiableAt ℝ (fun s : ℝ => heatOperator s u) t :=
  (heatOperator_hasDerivAt_convolution ht u).differentiableAt

/-- An explicit inverse-time bound on the strong L² derivative operator. -/
theorem timeDerivativeOperator_norm_le {t : ℝ} (ht : 0 < t) :
    ‖convolutionOperator (timeDerivativeKernel t) (timeDerivativeKernel_integrable ht)‖ ≤
      ((15/2:ℝ) * (2:ℝ)^((3:ℝ)/2)) * t⁻¹ :=
  (convolutionOperator_norm_le _ _).trans (timeDerivativeKernel_L1_bound ht)

/-- The strong L² derivative is the sum of the genuine ordered second spatial derivatives. -/
theorem heatOperator_hasDerivAt {t : ℝ} (ht : 0 < t) (u : L2Space) :
    HasDerivAt (fun s : ℝ => heatOperator s u)
      (∑ i : Fin 3, secondDerivativeOperator ht i i u) t := by
  simpa only [timeDerivativeOperator_eq_secondSum ht, sum_apply] using
    heatOperator_hasDerivAt_convolution ht u

/-- The actual H² Laplacian generates the strong heat evolution at positive times. -/
theorem heatOperator_hasDerivAt_laplace {t : ℝ} (ht : 0 < t) (u : L2Space) :
    HasDerivAt (fun s : ℝ => heatOperator s u)
      (SobolevGraph.H2.laplace (heatH2Path u t)) t := by
  rw [SobolevGraph.H2.laplace_eq, heatH2_secondSum_pos ht u]
  exact heatOperator_hasDerivAt_convolution ht u

theorem heatOperator_deriv_eq_laplace {t : ℝ} (ht : 0 < t) (u : L2Space) :
    deriv (fun s : ℝ => heatOperator s u) t = SobolevGraph.H2.laplace (heatH2Path u t) :=
  (heatOperator_hasDerivAt_laplace ht u).deriv

/-- The genuine strong derivative is continuous on positive time intervals. -/
theorem heatOperator_deriv_continuousOn (u : L2Space) :
    ContinuousOn (deriv (fun s : ℝ => heatOperator s u)) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => SobolevGraph.H2.laplace (heatH2Path u t)) (Ioi 0) :=
    SobolevGraph.H2.laplaceCLM.continuous.comp_continuousOn (heatH2Path_continuousOn u)
  exact hc.congr (fun t ht => heatOperator_deriv_eq_laplace ht u)

end UnforcedLeray.Heat
