import UnforcedLeray.Analysis.Heat.Translation
import UnforcedLeray.Analysis.Heat.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Strong continuity of the actual Gaussian average of L² translations

This is a Bochner integral in the ordinary Hilbert L² space. Its strong limit
at zero is proved by dominated convergence and translation continuity.
Identification with the raw spatial heat convolution is a separate theorem.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace UnforcedLeray.Heat

def orbitAverage (r : ℝ) (u : L2Space) : L2Space :=
  ∫ y : Space, Gaussian.kernel 1 y • translation (r • y) u

theorem orbitAverage_integrand_continuous (r : ℝ) (u : L2Space) :
    Continuous (fun y : Space => Gaussian.kernel 1 y • translation (r • y) u) :=
  (Gaussian.kernel_smooth 1).continuous.smul
    ((translation_continuous u).comp (show Continuous (fun y : Space => r • y) by fun_prop))

theorem orbitAverage_integrand_norm (r : ℝ) (u : L2Space) (y : Space) :
    ‖Gaussian.kernel 1 y • translation (r • y) u‖ = Gaussian.kernel 1 y * ‖u‖ := by
  rw [norm_smul, norm_translation,
    Real.norm_of_nonneg (Gaussian.kernel_nonneg (by norm_num) y)]

theorem orbitAverage_integrable (r : ℝ) (u : L2Space) :
    Integrable (fun y : Space => Gaussian.kernel 1 y • translation (r • y) u) := by
  apply ((Gaussian.kernel_integrable (by norm_num : (0 : ℝ) < 1)).mul_const ‖u‖).mono'
    (orbitAverage_integrand_continuous r u).aestronglyMeasurable
  exact Eventually.of_forall (fun y => (orbitAverage_integrand_norm r u y).le)

theorem orbitAverage_norm_le (r : ℝ) (u : L2Space) : ‖orbitAverage r u‖ ≤ ‖u‖ := by
  have h := norm_integral_le_of_norm_le
    ((Gaussian.kernel_integrable (by norm_num : (0 : ℝ) < 1)).mul_const ‖u‖)
    (Eventually.of_forall (fun y => (orbitAverage_integrand_norm r u y).le))
  simpa only [orbitAverage, integral_mul_const, Gaussian.integral_kernel (t := 1) (by norm_num),
    one_mul] using h

@[simp] theorem orbitAverage_zero (u : L2Space) : orbitAverage 0 u = u := by
  simp only [orbitAverage, zero_smul, translation_zero, integral_smul_const,
    Gaussian.integral_kernel (t := 1) (by norm_num), one_smul]

/-- Dominated convergence in actual L², with a fixed integrable Gaussian majorant. -/
theorem orbitAverage_continuous (u : L2Space) : Continuous (fun r : ℝ => orbitAverage r u) := by
  apply continuous_of_dominated (bound := fun y : Space => Gaussian.kernel 1 y * ‖u‖)
  · intro r
    exact (orbitAverage_integrand_continuous r u).aestronglyMeasurable
  · intro r
    exact Eventually.of_forall (fun y => (orbitAverage_integrand_norm r u y).le)
  · exact (Gaussian.kernel_integrable (by norm_num : (0 : ℝ) < 1)).mul_const ‖u‖
  · apply Eventually.of_forall
    intro y
    have hc : Continuous (fun r : ℝ => translation (r • y) u) :=
      (translation_continuous u).comp (show Continuous (fun r : ℝ => r • y) by fun_prop)
    exact (continuous_const : Continuous (fun _ : ℝ => Gaussian.kernel 1 y)).smul hc

theorem orbitAverage_add (r : ℝ) (u v : L2Space) :
    orbitAverage r (u+v) = orbitAverage r u + orbitAverage r v := by
  simp only [orbitAverage, map_add, smul_add]
  exact integral_add (orbitAverage_integrable r u) (orbitAverage_integrable r v)

theorem orbitAverage_smul (r a : ℝ) (u : L2Space) :
    orbitAverage r (a • u) = a • orbitAverage r u := by
  simp only [orbitAverage, map_smul, smul_comm (Gaussian.kernel 1 _) a]
  exact integral_smul a _

def orbitAverageLinear (r : ℝ) : L2Space →ₗ[ℝ] L2Space where
  toFun := orbitAverage r
  map_add' := orbitAverage_add r
  map_smul' := orbitAverage_smul r

/-- Gaussian orbit averaging is a contraction on the actual L² quotient. -/
def orbitAverageCLM (r : ℝ) : L2Space →L[ℝ] L2Space :=
  (orbitAverageLinear r).mkContinuous 1 (fun u => by
    change ‖orbitAverage r u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using orbitAverage_norm_le r u)

theorem orbitAverageCLM_norm_le (r : ℝ) : ‖orbitAverageCLM r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖orbitAverage r u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using orbitAverage_norm_le r u

/-- Strong approach to the identity in the standard heat-time parametrization. -/
theorem orbitAverage_heatTime_tendsto_zero (u : L2Space) :
    Tendsto (fun t : ℝ => orbitAverage (Real.sqrt (4*t)) u) (𝓝 0) (𝓝 u) := by
  have hc : Continuous (fun t : ℝ => orbitAverage (Real.sqrt (4*t)) u) :=
    (orbitAverage_continuous u).comp (by fun_prop)
  simpa only [mul_zero, Real.sqrt_zero, orbitAverage_zero] using
    hc.continuousAt.tendsto (x := (0 : ℝ))

end UnforcedLeray.Heat
