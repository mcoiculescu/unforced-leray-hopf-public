import UnforcedLeray.GaussianPotentialSup
import UnforcedLeray.GaussianTrial
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Smoothness across the Gaussian potential's removable point

The divided difference of the complex exponential is entire. Its restriction
to the real axis is nonzero, so its reciprocal is smooth and equals the
completed real ratio y/(exp(y)−1), including the value at zero. This proves
actual smoothness of W and Wlog without an assumed removable-singularity
regularity condition.
-/

noncomputable section
open Set
open scoped ContDiff Topology
namespace UnforcedLeray.Sturm
open GaussianPotential GaussianTrial

/-- The entire exponential divided difference restricts to the real one. -/
theorem complex_exp_dslope_ofReal (y : ℝ) :
    dslope Complex.exp 0 (y : ℂ) = ((dslope Real.exp 0 y : ℝ) : ℂ) := by
  by_cases hy : y = 0
  · subst y
    simp [dslope_same, Complex.deriv_exp, Real.deriv_exp]
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  rw [dslope_of_ne Complex.exp hyC, dslope_of_ne Real.exp hy]
  simp only [slope, vsub_eq_sub, sub_zero, Complex.exp_zero, Real.exp_zero, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub,
    Complex.ofReal_exp, Complex.ofReal_one]

/-- Complex removal of the apparent singularity proves global smoothness of
this actual real-valued divided difference. -/
theorem real_exp_dslope_smooth : ContDiff ℝ ∞ (dslope Real.exp 0) := by
  have hC : Differentiable ℂ (dslope Complex.exp 0) := by
    apply differentiableOn_univ.mp
    exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
      Complex.differentiable_exp.differentiableOn
  have hc : ContDiff ℝ ∞ (fun y : ℝ => (dslope Complex.exp 0 (y : ℂ)).re) :=
    hC.contDiff.real_of_complex
  have he : (fun y : ℝ => (dslope Complex.exp 0 (y : ℂ)).re) = dslope Real.exp 0 := by
    funext y
    rw [complex_exp_dslope_ofReal]
    rfl
  rwa [he] at hc

theorem real_exp_dslope_ne_zero (y : ℝ) : dslope Real.exp 0 y ≠ 0 := by
  by_cases hy : y = 0
  · simp [hy, Real.deriv_exp]
  have he : Real.exp y - 1 ≠ 0 := by
    intro he
    apply hy
    apply Real.exp_injective
    simpa only [Real.exp_zero] using sub_eq_zero.mp he
  rw [dslope_of_ne Real.exp hy]
  simpa only [slope, vsub_eq_sub, sub_zero, Real.exp_zero, smul_eq_mul] using
    mul_ne_zero (inv_ne_zero hy) he

/-- Equality of the completed quotient with a smooth reciprocal. -/
theorem bernoulliRatio_eq_inv_dslope (y : ℝ) :
    bernoulliRatio y = (dslope Real.exp 0 y)⁻¹ := by
  by_cases hy : y = 0
  · simp [hy, bernoulliRatio, Real.deriv_exp]
  rw [bernoulliRatio, ite_eq_right hy, dslope_of_ne Real.exp hy]
  simp [slope, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem bernoulliRatio_smooth : ContDiff ℝ ∞ bernoulliRatio := by
  rw [show bernoulliRatio = fun y => (dslope Real.exp 0 y)⁻¹ from
    funext bernoulliRatio_eq_inv_dslope]
  exact real_exp_dslope_smooth.inv real_exp_dslope_ne_zero

theorem W_eq_completed_ratio (y : ℝ) : W y = 4 * (y + 2) * bernoulliRatio y := by
  by_cases hy : y = 0
  · norm_num [hy, bernoulliRatio]
  · simp only [W, bernoulliRatio, hy, ↓reduceIte]
    ring

/-- The actual completed scalar potential is smooth at every real point. -/
theorem W_smooth : ContDiff ℝ ∞ W := by
  rw [show W = fun y => 4 * (y + 2) * bernoulliRatio y from funext W_eq_completed_ratio]
  exact (contDiff_const.mul (contDiff_id.add contDiff_const)).mul bernoulliRatio_smooth

/-- The concrete log-radius potential is globally C∞, including t=log(8)/2. -/
theorem Wlog_smooth : ContDiff ℝ ∞ Wlog := by
  unfold Wlog
  apply W_smooth.comp
  fun_prop

theorem continuous_Wlog : Continuous Wlog := Wlog_smooth.continuous

end UnforcedLeray.Sturm
