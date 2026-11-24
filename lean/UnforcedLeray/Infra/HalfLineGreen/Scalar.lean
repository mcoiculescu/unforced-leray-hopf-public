import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Scalar kernel integrals for the half-line Green operator

`paper/main.tex`, Section `sec:st18-329` (lines 432-434): "The kernels
`(1 + r^{-1/2}) e^{-(β-β₋) r}` and `e^{-(β₊-β) r}` are integrable."

* `setIntegral_Iio_eq_Ioi`, `integrableOn_Iio_iff`: the reflection `s = τ - r` turning a past
  integral `∫_{-∞}^τ` into an integral over `r ∈ (0, ∞)`;
* `integral_exp_neg_mul_Ioi`: `∫_0^∞ e^{-a r} dr = 1/a`;
* `integral_pastProfile`: `∫_0^∞ (1 + r^{-1/2}) e^{-a r} dr = 1/a + (1/a)^{1/2} Γ(1/2)`;
* `intervalIntegral_exp_neg_mul_sub_le`: `∫_τ^{τ₀} e^{-b(s-τ)} ds ≤ 1/b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Infra.HalfLineGreen

section Reflection

variable {E : Type*} [NormedAddCommGroup E]

theorem measurePreserving_sub_left_real (τ : ℝ) :
    MeasurePreserving (fun s : ℝ => τ - s) volume volume :=
  Measure.measurePreserving_sub_left volume τ

theorem measurableEmbedding_sub_left_real (τ : ℝ) : MeasurableEmbedding (fun s : ℝ => τ - s) :=
  (MeasurableEquiv.subLeft τ).measurableEmbedding

theorem preimage_sub_left_Ioi_zero (τ : ℝ) : (fun s : ℝ => τ - s) ⁻¹' Ioi 0 = Iio τ := by
  ext s
  simp

/-- Integrability over the past `(-∞, τ)` is integrability of the reflected function over
`(0, ∞)`. -/
theorem integrableOn_Iio_iff (τ : ℝ) {g : ℝ → E} :
    IntegrableOn g (Iio τ) ↔ IntegrableOn (fun r => g (τ - r)) (Ioi 0) := by
  have h := (measurePreserving_sub_left_real τ).integrableOn_comp_preimage
    (measurableEmbedding_sub_left_real τ) (f := fun r => g (τ - r)) (s := Ioi 0)
  rw [preimage_sub_left_Ioi_zero] at h
  rw [← h]
  simp only [Function.comp_def, sub_sub_cancel]

/-- The reflection `s = τ - r`: `∫_{-∞}^τ g(s) ds = ∫_0^∞ g(τ - r) dr`. -/
theorem setIntegral_Iio_eq_Ioi [NormedSpace ℝ E] (τ : ℝ) (g : ℝ → E) :
    ∫ s in Iio τ, g s = ∫ r in Ioi 0, g (τ - r) := by
  have h := (measurePreserving_sub_left_real τ).setIntegral_preimage_emb
    (measurableEmbedding_sub_left_real τ) (fun r => g (τ - r)) (Ioi 0)
  rw [preimage_sub_left_Ioi_zero] at h
  rw [← h]
  simp only [sub_sub_cancel]

end Reflection

/-- `∫_0^∞ e^{-a r} dr`-integrability for `a > 0`. -/
theorem integrableOn_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => exp (-(a * r))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := a)
    (by norm_num) one_pos ha
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [rpow_zero, rpow_one, one_mul, neg_mul]

/-- `∫_0^∞ e^{-a r} dr = 1/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), exp (-(a * r)) = 1 / a := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := a) one_pos ha
  rw [sub_self, Gamma_one, rpow_one, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  simp only [rpow_zero, one_mul]

/-- The square-root Gamma integrand `r^{-1/2} e^{-a r}` is integrable on `(0, ∞)`. -/
theorem integrableOn_rpow_neg_half_mul_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ (-(1 / 2 : ℝ)) * exp (-(a * r))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ)) (b := a)
    (by norm_num) one_pos ha
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [rpow_one, neg_mul]

/-- `∫_0^∞ r^{-1/2} e^{-a r} dr = (1/a)^{1/2} Γ(1/2)`. -/
theorem integral_rpow_neg_half_mul_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), r ^ (-(1 / 2 : ℝ)) * exp (-(a * r)) = (1 / a) ^ (1 / 2 : ℝ) * Gamma (1 / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := a) (by norm_num) ha
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at h
  exact h

/-- The profile `(1 + r^{-1/2}) e^{-a r}` of the past kernel. -/
def pastProfile (a r : ℝ) : ℝ := (1 + r ^ (-(1 / 2 : ℝ))) * exp (-(a * r))

theorem pastProfile_nonneg (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ pastProfile a r :=
  mul_nonneg (add_nonneg zero_le_one (rpow_nonneg hr _)) (exp_pos _).le

theorem integrableOn_pastProfile {a : ℝ} (ha : 0 < a) : IntegrableOn (pastProfile a) (Ioi 0) := by
  have h := (integrableOn_exp_neg_mul ha).add (integrableOn_rpow_neg_half_mul_exp_neg_mul ha)
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [pastProfile, Pi.add_apply]
  ring

/-- `∫_0^∞ (1 + r^{-1/2}) e^{-a r} dr = 1/a + (1/a)^{1/2} Γ(1/2)`. -/
theorem integral_pastProfile {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), pastProfile a r = 1 / a + (1 / a) ^ (1 / 2 : ℝ) * Gamma (1 / 2) := by
  rw [← integral_rpow_neg_half_mul_exp_neg_mul ha, ← integral_exp_neg_mul_Ioi ha,
    ← integral_add (integrableOn_exp_neg_mul ha) (integrableOn_rpow_neg_half_mul_exp_neg_mul ha)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  simp only [pastProfile]
  ring

/-- `∫_τ^{τ₀} e^{-b(s - τ)} ds ≤ 1/b` for `b > 0`, `τ ≤ τ₀`. -/
theorem intervalIntegral_exp_neg_mul_sub_le {b : ℝ} (hb : 0 < b) {τ τ₀ : ℝ} (h : τ ≤ τ₀) :
    ∫ s in τ..τ₀, exp (-(b * (s - τ))) ≤ 1 / b := by
  rw [intervalIntegral.integral_comp_sub_right (fun r => exp (-(b * r))) τ, sub_self,
    intervalIntegral.integral_of_le (by linarith), ← integral_exp_neg_mul_Ioi hb]
  refine setIntegral_mono_set (integrableOn_exp_neg_mul hb) ?_ ?_
  · filter_upwards with r
    exact (exp_pos _).le
  · exact Ioc_subset_Ioi_self.eventuallyLE

end UnforcedLeray.Infra.HalfLineGreen
