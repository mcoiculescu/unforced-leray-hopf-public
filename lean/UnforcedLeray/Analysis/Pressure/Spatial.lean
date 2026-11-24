import UnforcedLeray.Analysis.Pressure.NewtonKernel
import UnforcedLeray.Analysis.Pressure.Young
import UnforcedLeray.Analysis.Pressure.VelocityForcing
import UnforcedLeray.Analysis.Pressure.Optimize
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The actual spatial Newtonian pressure of a weak H¹ field

The scalar function is the sum of three real Bochner convolutions with the
normalized Newtonian-gradient kernel. Its defining integrals exist almost
everywhere. Near/far Young estimates prove finite L^(5/3) membership; choosing
the radius A / D proves the energy-scale norm bound. The zero cases are proved
from vanishing forcing. The distributional pressure equation is established
separately and is not an assumption of these analytic estimates.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace UnforcedLeray.PressureAnalysis

/-- One literal, real Newtonian-gradient convolution. -/
def newtonComponent (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  ∫ y, newtonGradientKernel i (x - y) * f y

/-- The literal scalar potential built from the actual convective forcing. -/
def velocityPressure (u : SpatialField) (g : Fin 3 → SpatialField) (x : Space) : ℝ :=
  ∑ i : Fin 3, newtonComponent i (velocityForcing u g i) x

private theorem near_integrable_ae {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf : MemLp f (3 / 2) volume) :
    ∀ᵐ x, Integrable (fun y => nearNewtonKernel R i (x - y) * f y) volume :=
  convolution_integrable_ae_near (nearNewtonKernel_memLp hR i) hf

private theorem far_integrable_ae {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf : MemLp f 1 volume) :
    ∀ᵐ x, Integrable (fun y => farNewtonKernel R i (x - y) * f y) volume :=
  convolution_integrable_ae_far (farNewtonKernel_memLp hR i) hf

private theorem near_memLp {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf : MemLp f (3 / 2) volume) :
    MemLp (fun x => ∫ y, nearNewtonKernel R i (x - y) * f y) (5 / 3) volume :=
  convolution_memLp_near (nearNewtonKernel_memLp hR i) hf

private theorem far_memLp {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf : MemLp f 1 volume) :
    MemLp (fun x => ∫ y, farNewtonKernel R i (x - y) * f y) (5 / 3) volume :=
  convolution_memLp_far (farNewtonKernel_memLp hR i) hf

private theorem near_norm_le {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf : MemLp f (3 / 2) volume) :
    (eLpNorm (fun x => ∫ y, nearNewtonKernel R i (x - y) * f y) (5 / 3) volume).toReal ≤
      (newtonNearConstant * R ^ (4 / 5 : ℝ)) * (eLpNorm f (3 / 2) volume).toReal :=
  (convolution_norm_le_near (nearNewtonKernel_memLp hR i) hf).trans
    (mul_le_mul_of_nonneg_right (nearNewtonKernel_eLpNorm_toReal_le hR i)
      ENNReal.toReal_nonneg)

private theorem far_norm_le {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf : MemLp f 1 volume) :
    (eLpNorm (fun x => ∫ y, farNewtonKernel R i (x - y) * f y) (5 / 3) volume).toReal ≤
      (newtonFarConstant * R ^ (-1 / 5 : ℝ)) * (eLpNorm f 1 volume).toReal :=
  (convolution_norm_le_far (farNewtonKernel_memLp hR i) hf).trans
    (mul_le_mul_of_nonneg_right (farNewtonKernel_eLpNorm_toReal_le hR i)
      ENNReal.toReal_nonneg)

/-- Each whole-kernel convolution is absolutely integrable almost everywhere. -/
theorem newtonComponent_integrable_ae (i : Fin 3) {f : Space → ℝ}
    (hf1 : MemLp f 1 volume) (hf3 : MemLp f (3 / 2) volume) :
    ∀ᵐ x, Integrable (fun y => newtonGradientKernel i (x - y) * f y) volume := by
  filter_upwards [near_integrable_ae (by norm_num : (0 : ℝ) < 1) i hf3,
    far_integrable_ae (by norm_num : (0 : ℝ) < 1) i hf1] with x hn hf
  have he : (fun y => newtonGradientKernel i (x - y) * f y) =
      (fun y => nearNewtonKernel 1 i (x - y) * f y + farNewtonKernel 1 i (x - y) * f y) := by
    funext y
    rw [← add_mul, nearNewtonKernel_add_far]
  rw [he]
  exact hn.add hf

/-- Every positive splitting radius gives the same actual convolution a.e. -/
theorem newtonComponent_eq_split_ae {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf1 : MemLp f 1 volume) (hf3 : MemLp f (3 / 2) volume) :
    newtonComponent i f =ᵐ[volume] fun x =>
      (∫ y, nearNewtonKernel R i (x - y) * f y) +
        ∫ y, farNewtonKernel R i (x - y) * f y := by
  filter_upwards [near_integrable_ae hR i hf3, far_integrable_ae hR i hf1] with x hn hf
  rw [newtonComponent, ← integral_add hn hf]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by dsimp only; rw [← add_mul, nearNewtonKernel_add_far]

/-- Genuine finite L^(5/3) membership of the unsplit convolution. -/
theorem newtonComponent_memLp (i : Fin 3) {f : Space → ℝ}
    (hf1 : MemLp f 1 volume) (hf3 : MemLp f (3 / 2) volume) :
    MemLp (newtonComponent i f) (5 / 3) volume := by
  have h := (near_memLp (by norm_num : (0 : ℝ) < 1) i hf3).add
    (far_memLp (by norm_num : (0 : ℝ) < 1) i hf1)
  exact h.ae_eq (newtonComponent_eq_split_ae (by norm_num : (0 : ℝ) < 1) i hf1 hf3).symm

/-- The actual norm is bounded by the near/far estimates at every positive radius. -/
theorem newtonComponent_norm_le {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {f : Space → ℝ} (hf1 : MemLp f 1 volume) (hf3 : MemLp f (3 / 2) volume) :
    (eLpNorm (newtonComponent i f) (5 / 3) volume).toReal ≤
      (newtonNearConstant * R ^ (4 / 5 : ℝ)) * (eLpNorm f (3 / 2) volume).toReal +
        (newtonFarConstant * R ^ (-1 / 5 : ℝ)) * (eLpNorm f 1 volume).toReal := by
  have hn := near_memLp hR i hf3
  have hf := far_memLp hR i hf1
  rw [eLpNorm_congr_ae (newtonComponent_eq_split_ae hR i hf1 hf3)]
  have hs := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hn.2.ne, hf.2.ne⟩)
    (eLpNorm_add_le hn.1 hf.1 (by norm_num [ENNReal.le_div_iff_mul_le] : (1 : ℝ≥0∞) ≤ 5 / 3))
  rw [ENNReal.toReal_add hn.2.ne hf.2.ne] at hs
  exact hs.trans (add_le_add (near_norm_le hR i hf3) (far_norm_le hR i hf1))

/-- Vanishing forcing gives the zero convolution everywhere, including exceptional x. -/
theorem newtonComponent_eq_zero_of_ae_zero (i : Fin 3) {f : Space → ℝ}
    (hf : f =ᵐ[volume] 0) : newtonComponent i f = 0 := by
  funext x
  change (∫ y, newtonGradientKernel i (x - y) * f y) = 0
  rw [integral_eq_zero_of_ae]
  filter_upwards [hf] with y hy
  simp [hy]

/-- Actual real pressure has finite L^(5/3) norm for every weak H¹ velocity. -/
theorem velocityPressure_memLp {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i)) :
    MemLp (velocityPressure u g) (5 / 3) volume := by
  exact memLp_finsetSum Finset.univ (fun i _ => newtonComponent_memLp i
    (velocityForcing_memLp_one hu hg i) (velocityForcing_memLp_threeHalves hu hg hweak i))

/-- Each integral used in the actual pressure exists almost everywhere. -/
theorem velocityPressure_integrals_exist_ae {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i)) :
    ∀ᵐ x, ∀ i : Fin 3,
      Integrable (fun y => newtonGradientKernel i (x - y) * velocityForcing u g i y) volume :=
  ae_all_iff.mpr (fun i => newtonComponent_integrable_ae i
    (velocityForcing_memLp_one hu hg i) (velocityForcing_memLp_threeHalves hu hg hweak i))

/-- The fixed coefficient of the energy-scale spatial pressure estimate. -/
def velocityPressureConstant : ℝ :=
  3 * (newtonNearConstant * (SobolevEmbedding.sobolevConstant : ℝ) + newtonFarConstant)

theorem velocityPressureConstant_nonneg : 0 ≤ velocityPressureConstant := by
  unfold velocityPressureConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg newtonNearConstant_nonneg (by positivity)) newtonFarConstant_nonneg)

private theorem velocityPressure_norm_sum_le {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i)) :
    (eLpNorm (velocityPressure u g) (5 / 3) volume).toReal ≤
      ∑ i : Fin 3, (eLpNorm (newtonComponent i (velocityForcing u g i)) (5 / 3) volume).toReal := by
  have hm (i : Fin 3) := newtonComponent_memLp i (velocityForcing_memLp_one hu hg i)
    (velocityForcing_memLp_threeHalves hu hg hweak i)
  have hs := eLpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => (hm i).1)
    (by norm_num [ENNReal.le_div_iff_mul_le] : (1 : ℝ≥0∞) ≤ 5 / 3)
  have hfinite : (∑ i : Fin 3, eLpNorm (newtonComponent i (velocityForcing u g i)) (5 / 3) volume) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun i _ => (hm i).2)).ne
  have ht := ENNReal.toReal_mono hfinite hs
  have he : velocityPressure u g = ∑ i : Fin 3, newtonComponent i (velocityForcing u g i) := by
    ext x
    simp [velocityPressure]
  rw [he]
  simpa only [ENNReal.toReal_sum (fun i _ => (hm i).2.ne)] using ht

/-- Quantitative splitting estimate before choosing the energy-dependent radius. -/
theorem velocityPressure_norm_le_radius {R : ℝ} (hR : 0 < R)
    {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i)) :
    (eLpNorm (velocityPressure u g) (5 / 3) volume).toReal ≤
      3 * ((newtonNearConstant * (SobolevEmbedding.sobolevConstant : ℝ)) *
        R ^ (4 / 5 : ℝ) * (∑ i : Fin 3, l2Norm (g i)) ^ 2 +
        newtonFarConstant * R ^ (-1 / 5 : ℝ) *
          (l2Norm u * ∑ i : Fin 3, l2Norm (g i))) := by
  apply (velocityPressure_norm_sum_le hu hg hweak).trans
  have hterm (i : Fin 3) :
      (eLpNorm (newtonComponent i (velocityForcing u g i)) (5 / 3) volume).toReal ≤
      (newtonNearConstant * (SobolevEmbedding.sobolevConstant : ℝ)) *
        R ^ (4 / 5 : ℝ) * (∑ i : Fin 3, l2Norm (g i)) ^ 2 +
        newtonFarConstant * R ^ (-1 / 5 : ℝ) *
          (l2Norm u * ∑ i : Fin 3, l2Norm (g i)) := by
    apply (newtonComponent_norm_le hR i (velocityForcing_memLp_one hu hg i)
      (velocityForcing_memLp_threeHalves hu hg hweak i)).trans
    have hn := mul_le_mul_of_nonneg_left (velocityForcing_norm_threeHalves_le hu hg hweak i)
      (mul_nonneg newtonNearConstant_nonneg (Real.rpow_nonneg hR.le (4 / 5 : ℝ)))
    have hf := mul_le_mul_of_nonneg_left (velocityForcing_norm_one_le hu hg i)
      (mul_nonneg newtonFarConstant_nonneg (Real.rpow_nonneg hR.le (-1 / 5 : ℝ)))
    convert add_le_add hn hf using 1; ring
  simpa [← mul_add] using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hterm i)

private theorem velocityPressure_eq_zero_of_energy_zero
    {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hz : l2Norm u = 0 ∨ (∑ i : Fin 3, l2Norm (g i)) = 0) :
    velocityPressure u g = 0 := by
  have hzero (i : Fin 3) : velocityForcing u g i =ᵐ[volume] 0 :=
    velocityForcing_ae_zero_of_energy_norm_zero hu hg hz i
  funext x
  simp only [velocityPressure]
  have h (i : Fin 3) := congrFun (newtonComponent_eq_zero_of_ae_zero i (hzero i)) x
  simp only [h, Pi.zero_apply, Finset.sum_const_zero]

/-- The actual pressure has the exact energy-scale spatial L^(5/3) bound. -/
theorem velocityPressure_norm_le {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i)) :
    (eLpNorm (velocityPressure u g) (5 / 3) volume).toReal ≤
      velocityPressureConstant * l2Norm u ^ (4 / 5 : ℝ) *
        (∑ i : Fin 3, l2Norm (g i)) ^ (6 / 5 : ℝ) := by
  have hA : 0 ≤ l2Norm u := ENNReal.toReal_nonneg
  have hD : 0 ≤ ∑ i : Fin 3, l2Norm (g i) :=
    Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
  by_cases hz : l2Norm u = 0 ∨ (∑ i : Fin 3, l2Norm (g i)) = 0
  · rw [velocityPressure_eq_zero_of_energy_zero hu hg hz, eLpNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (mul_nonneg velocityPressureConstant_nonneg (Real.rpow_nonneg hA _))
      (Real.rpow_nonneg hD _)
  · have hA' : 0 < l2Norm u := lt_of_le_of_ne hA (Ne.symm (not_or.mp hz).1)
    have hD' : 0 < ∑ i : Fin 3, l2Norm (g i) := lt_of_le_of_ne hD (Ne.symm (not_or.mp hz).2)
    have h := velocityPressure_norm_le_radius (div_pos hA' hD') hu hg hweak
    rw [balanced_sum hA' hD'] at h
    simpa only [velocityPressureConstant, mul_assoc] using h

/-- The finite pressure norm has the exact powers integrated by the energy estimate. -/
theorem velocityPressure_norm_rpow_le {u : SpatialField} {g : Fin 3 → SpatialField}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i)) :
    (eLpNorm (velocityPressure u g) (5 / 3) volume).toReal ^ (5 / 3 : ℝ) ≤
      velocityPressureConstant ^ (5 / 3 : ℝ) * l2Norm u ^ (4 / 3 : ℝ) *
        (∑ i : Fin 3, l2Norm (g i)) ^ 2 := by
  have h := Real.rpow_le_rpow ENNReal.toReal_nonneg (velocityPressure_norm_le hu hg hweak)
    (by norm_num : (0 : ℝ) ≤ 5 / 3)
  rw [pressure_energy_power (A := l2Norm u) (D := ∑ i : Fin 3, l2Norm (g i))
    velocityPressureConstant_nonneg ENNReal.toReal_nonneg
    (Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg))] at h
  exact h

end UnforcedLeray.PressureAnalysis
