/-
Adapted from OpenAI's NavierStokesAndEuler, Euler/WholeSpaceGaussian.lean,
commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd. Apache-2.0.
Changes: imports and namespace; uses the project's actual Euclidean R³.
-/
import UnforcedLeray.Statement
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-!
# Actual normalized Gaussian on three-dimensional Euclidean space

The variance parameter here is q>0 with kernel (πq)^(-3/2)exp(-|x|²/q).
The standard viscosity-one heat kernel at time t is kernel (4*t), defined below.
All mass and finite-norm assertions are proved for these concrete functions.
-/
noncomputable section
namespace UnforcedLeray.Heat.Gaussian
open MeasureTheory InnerProductSpace Filter
open scoped ContDiff ENNReal RealInnerProductSpace

def normalization (t : ℝ) : ℝ := (Real.pi*t)^(-(3:ℝ)/2)

def kernel (t : ℝ) (x : Space) : ℝ :=
  normalization t * Real.exp (-t⁻¹*‖x‖^2)

theorem normalization_pos {t : ℝ} (ht : 0 < t) : 0 < normalization t :=
  Real.rpow_pos_of_pos (mul_pos Real.pi_pos ht) _

theorem kernel_pos {t : ℝ} (ht : 0 < t) (x : Space) : 0 < kernel t x :=
  mul_pos (normalization_pos ht) (Real.exp_pos _)

theorem kernel_nonneg {t : ℝ} (ht : 0 < t) (x : Space) : 0 ≤ kernel t x :=
  (kernel_pos ht x).le

theorem kernel_le_normalization {t : ℝ} (ht : 0 < t) (x : Space) :
    kernel t x ≤ normalization t := by
  unfold kernel
  apply mul_le_of_le_one_right (normalization_pos ht).le
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (inv_pos.mpr ht).le) (sq_nonneg ‖x‖))

theorem kernel_smooth (t : ℝ) : ContDiff ℝ ∞ (kernel t) := by
  unfold kernel
  have hn : ContDiff ℝ ∞ (fun x : Space => ‖x‖^2) := contDiff_id.norm_sq ℝ
  exact contDiff_const.mul ((contDiff_const.mul hn).exp)

theorem exp_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Space => Real.exp (-b*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Space) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun x : Space => (Complex.exp
    (-(b : ℂ)*‖x‖^2 + 0*inner ℝ (0 : Space) x)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h

theorem kernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (kernel t) :=
  (exp_integrable (inv_pos.mpr ht)).const_mul _

theorem integral_kernel {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, kernel t x) = 1 := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  simp only [kernel]
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (inv_pos.mpr ht), hdim]
  simp only [Nat.cast_ofNat, div_inv_eq_mul]
  unfold normalization
  rw [← Real.rpow_add (mul_pos Real.pi_pos ht)]
  norm_num

theorem kernel_sq_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Space => kernel t x ^ 2) := by
  apply ((kernel_integrable ht).const_mul (normalization t)).mono'
    ((kernel_smooth t).continuous.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖kernel t x ^ 2‖ ≤ normalization t * kernel t x
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (kernel_le_normalization ht x) (kernel_nonneg ht x)

theorem kernel_memLp {t : ℝ} (ht : 0 < t) : MemLp (kernel t) 2 volume :=
  (memLp_two_iff_integrable_sq (kernel_smooth t).continuous.aestronglyMeasurable).2
    (kernel_sq_integrable ht)

theorem integral_kernel_sq_le {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, kernel t x ^ 2) ≤ normalization t := by
  calc
    _ ≤ ∫ x : Space, normalization t * kernel t x :=
      integral_mono (kernel_sq_integrable ht) ((kernel_integrable ht).const_mul _)
        (fun x => by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_right (kernel_le_normalization ht x) (kernel_nonneg ht x))
    _ = normalization t := by rw [integral_const_mul, integral_kernel ht, mul_one]

theorem sqrt_normalization {t : ℝ} (ht : 0 < t) :
    Real.sqrt (normalization t) = (Real.pi*t)^(-(3:ℝ)/4) := by
  rw [Real.sqrt_eq_rpow, normalization, ← Real.rpow_mul (mul_pos Real.pi_pos ht).le]
  norm_num

theorem sqrt_normalization_le {t : ℝ} (ht : 0 < t) :
    Real.sqrt (normalization t) ≤ t^(-(3:ℝ)/4) := by
  rw [sqrt_normalization ht]
  apply Real.rpow_le_rpow_of_nonpos ht
  · nlinarith [Real.pi_pos, Real.two_le_pi]
  · norm_num


end UnforcedLeray.Heat.Gaussian
