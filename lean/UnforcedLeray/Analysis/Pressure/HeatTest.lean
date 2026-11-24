import UnforcedLeray.Analysis.Heat.AveragingEvolution
import UnforcedLeray.TestFunctions
import UnforcedLeray.Analysis.Heat.GaussianScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Scalar compact tests against the genuine heat kernel

The heat pairing evolves by the actual Laplacian of the test. The derivative
is transferred from the Gaussian by two justified integrations by parts.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal
namespace UnforcedLeray.PressureAnalysis

/-- The literal scalar heat pairing at the spatial origin. -/
def heatTestPairing (φ : Space → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Space, Heat.kernel t x * φ x

theorem contDiff_spatialTestDerivative {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (spatialTestDerivative i f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem integral_partial_mul_test {f φ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : IsSpatialTest φ) (i : Fin 3) :
    (∫ x : Space, spatialTestDerivative i f x * φ x) =
      -(∫ x : Space, f x * spatialTestDerivative i φ x) := by
  have hdf := contDiff_spatialTestDerivative hf i
  have hdφ := hφ.derivative i
  have h1 : Integrable (fun x : Space => spatialTestDerivative i f x * φ x) :=
    (hdf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left
  have h2 : Integrable (fun x : Space => f x * spatialTestDerivative i φ x) :=
    (hf.continuous.mul hdφ.continuous).integrable_of_hasCompactSupport hdφ.compact.mul_left
  have h0 : Integrable (fun x : Space => f x * φ x) :=
    (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := coordinateVector i) h1 h2 h0
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hφ.smooth.differentiable (by simp)).differentiableAt)
  exact neg_eq_iff_eq_neg.mp hi.symm

theorem integral_secondPartial_mul_test {f φ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : IsSpatialTest φ) (i : Fin 3) :
    (∫ x : Space, spatialTestDerivative i (spatialTestDerivative i f) x * φ x) =
      ∫ x : Space, f x * spatialTestDerivative i (spatialTestDerivative i φ) x := by
  rw [integral_partial_mul_test (contDiff_spatialTestDerivative hf i) hφ i,
    integral_partial_mul_test hf (hφ.derivative i) i, neg_neg]

/-- Compact-test integration by parts for the actual coordinate Laplacian. -/
theorem integral_laplacian_mul_test {f φ : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : IsSpatialTest φ) :
    (∫ x : Space, Heat.laplacian f x * φ x) =
      ∫ x : Space, f x * Heat.laplacian φ x := by
  have hi1 (i : Fin 3) :
      Integrable (fun x : Space => spatialTestDerivative i (spatialTestDerivative i f) x * φ x) :=
    ((contDiff_spatialTestDerivative (contDiff_spatialTestDerivative hf i) i).continuous.mul
      hφ.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left
  have hi2 (i : Fin 3) :
      Integrable (fun x : Space => f x * spatialTestDerivative i (spatialTestDerivative i φ) x) :=
    (hf.continuous.mul ((hφ.derivative i).derivative i).continuous).integrable_of_hasCompactSupport
      ((hφ.derivative i).derivative i).compact.mul_left
  change (∫ x : Space, (∑ i : Fin 3, spatialTestDerivative i (spatialTestDerivative i f) x) * φ x) =
    ∫ x : Space, f x * (∑ i : Fin 3, spatialTestDerivative i (spatialTestDerivative i φ) x)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi1 i), integral_finsetSum _ (fun i _ => hi2 i)]
  exact Finset.sum_congr rfl (fun i _ => integral_secondPartial_mul_test hf hφ i)

/-- The actual scalar Laplacian preserves smooth compact test functions. -/
theorem scalarTest_laplacian {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    IsSpatialTest (Heat.laplacian φ) := by
  have he : Heat.laplacian φ = ∑ i : Fin 3,
      spatialTestDerivative i (spatialTestDerivative i φ) := rfl
  rw [he]
  constructor
  · convert (ContDiff.sum (s := Finset.univ)
      (fun i _ => ((hφ.derivative i).derivative i).smooth)) using 1
    funext x
    simp only [Finset.sum_apply]
  · exact HasCompactSupport.finset_sum (fun i _ => ((hφ.derivative i).derivative i).compact)

/-- The actual test heat pairing has derivative equal to the heat pairing
of the test's Laplacian, with no PDE hypothesis on the test. -/
theorem heatTestPairing_hasDerivAt {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatTestPairing φ)
      (∫ x : Space, Heat.kernel t x * Heat.laplacian φ x) t := by
  have hr : IsSpatialTest (fun x : Space => φ (-x)) :=
    ⟨hφ.smooth.comp contDiff_neg, hφ.compact.comp_homeomorph (Homeomorph.neg Space)⟩
  have hd := Heat.average_hasDerivAt_laplacianKernel ht (hr.memLp 2) (0 : Space)
  have he : (∫ x : Space, Heat.laplacian (Heat.kernel t) x * φ x) =
      ∫ x : Space, Heat.kernel t x * Heat.laplacian φ x :=
    integral_laplacian_mul_test (Heat.Gaussian.kernel_smooth (4*t)) hφ
  change HasDerivAt (fun s => ∫ y : Space, Heat.kernel s y * φ y) _ t
  convert hd using 1 <;> try rfl
  · funext s
    simp only [Heat.average, zero_sub, neg_neg, smul_eq_mul]
  · simpa only [zero_sub, neg_neg, smul_eq_mul] using he.symm

def scaledHeatTestPairing (φ : Space → ℝ) (t : ℝ) : ℝ :=
  ∫ y : Space, Heat.Gaussian.kernel 1 y * φ (Real.sqrt (4*t) • y)

theorem scaledHeatTestPairing_eq {t : ℝ} (ht : 0 < t) (φ : Space → ℝ) :
    scaledHeatTestPairing φ t = heatTestPairing φ t := by
  let r := Real.sqrt (4*t)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity : 0 < 4*t)
  have he (y : Space) : Heat.kernel t (r • y) =
      (r ^ 3)⁻¹ * Heat.Gaussian.kernel 1 y := by
    have h := Heat.Gaussian.kernel_squareScale hr y
    simpa only [r, Heat.kernel, Real.sq_sqrt (by positivity : 0 ≤ 4*t)] using h
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun y : Space => Heat.kernel t y * φ y) r (hR := hr.le)
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [he, mul_assoc, integral_const_mul, hdim, smul_eq_mul] at h
  change (r ^ 3)⁻¹ * scaledHeatTestPairing φ t =
    (r ^ 3)⁻¹ * heatTestPairing φ t at h
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 hr.ne')) h

theorem scaledHeatTestPairing_zero (φ : Space → ℝ) :
    scaledHeatTestPairing φ 0 = φ 0 := by
  simp only [scaledHeatTestPairing, mul_zero, Real.sqrt_zero, zero_smul,
    integral_mul_const, Heat.Gaussian.integral_kernel (by norm_num : (0:ℝ)<1), one_mul]

theorem scaledHeatTestPairing_continuous {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    Continuous (scaledHeatTestPairing φ) := by
  obtain ⟨C,hC⟩ := hφ.compact.exists_bound_of_continuous hφ.continuous
  apply continuous_of_dominated (bound := fun y : Space => Heat.Gaussian.kernel 1 y*C)
  · intro t
    exact ((Heat.Gaussian.kernel_smooth 1).continuous.mul
      (hφ.continuous.comp (show Continuous (fun y : Space => Real.sqrt (4*t) • y) by fun_prop))).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall (fun y => by
      rw [norm_mul, Real.norm_of_nonneg (Heat.Gaussian.kernel_nonneg (by norm_num : (0:ℝ)<1) y)]
      exact mul_le_mul_of_nonneg_left (hC _) (Heat.Gaussian.kernel_nonneg (by norm_num) y))
  · exact (Heat.Gaussian.kernel_integrable (by norm_num : (0:ℝ)<1)).mul_const C
  · exact Eventually.of_forall (fun y =>
      continuous_const.mul (hφ.continuous.comp
        (show Continuous (fun t : ℝ => Real.sqrt (4*t) • y) by fun_prop)))

theorem heatTestPairing_tendsto_zero {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    Tendsto (heatTestPairing φ) (𝓝[>] 0) (𝓝 (φ 0)) := by
  have h : Tendsto (scaledHeatTestPairing φ) (𝓝[>] 0)
      (𝓝 (scaledHeatTestPairing φ 0)) :=
    (scaledHeatTestPairing_continuous hφ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [scaledHeatTestPairing_zero] at h
  exact h.congr' (eventually_nhdsWithin_of_forall (fun t ht => scaledHeatTestPairing_eq ht φ))

theorem heatTestPairing_norm_le {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {t : ℝ} (ht : 0 < t) :
    ‖heatTestPairing φ t‖ ≤ Heat.Gaussian.normalization (4*t) * ∫ x : Space, ‖φ x‖ := by
  have h := norm_integral_le_of_norm_le
    (hφ.integrable.norm.const_mul (Heat.Gaussian.normalization (4*t)))
    (f := fun x : Space => Heat.kernel t x * φ x)
    (Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_of_nonneg (Heat.kernel_nonneg ht x)]
      exact mul_le_mul_of_nonneg_right
        (Heat.Gaussian.kernel_le_normalization (by positivity : 0 < 4*t) x) (norm_nonneg _)))
  simpa only [heatTestPairing, integral_const_mul] using h

theorem heatTestPairing_tendsto_atTop {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    Tendsto (heatTestPairing φ) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun t : ℝ => Heat.Gaussian.normalization (4*t)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/2)).comp
      (tendsto_id.const_mul_atTop (by positivity : 0 < 4*Real.pi))
    simpa only [Function.comp_def, id_eq, Heat.Gaussian.normalization, neg_div, mul_comm 4 Real.pi, mul_assoc] using h
  apply squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun t ht => heatTestPairing_norm_le hφ (by linarith)⟩)
  simpa only [zero_mul] using hnorm.mul_const (∫ x : Space, ‖φ x‖)


theorem scaledHeatTestPairing_hasDerivAt {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scaledHeatTestPairing φ)
      (heatTestPairing (Heat.laplacian φ) t) t := by
  apply (heatTestPairing_hasDerivAt hφ ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact scaledHeatTestPairing_eq hs φ

theorem scaledHeatTestPairing_tendsto_atTop {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    Tendsto (scaledHeatTestPairing φ) atTop (𝓝 0) := by
  apply (heatTestPairing_tendsto_atTop hφ).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (scaledHeatTestPairing_eq ht φ).symm

theorem integral_heatTestPairing_laplacian_eq {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    (hint : IntegrableOn (heatTestPairing (Heat.laplacian φ)) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), heatTestPairing (Heat.laplacian φ) t) = -φ 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (m := (0 : ℝ))
    (scaledHeatTestPairing_continuous hφ).continuousAt.continuousWithinAt
    (fun t ht => scaledHeatTestPairing_hasDerivAt hφ ht) hint
    (scaledHeatTestPairing_tendsto_atTop hφ)
  simpa only [scaledHeatTestPairing_zero, zero_sub] using h

end UnforcedLeray.PressureAnalysis
