import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Actual Dirichlet energy identity for complex interval modes

The second derivative pairing is evaluated by integration by parts, with the
boundary term proved zero from Dirichlet data. Every pairing and energy term
is integrable on the finite interval by the stated C² regularity.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace UnforcedLeray.Rayleigh

/-- The mode-two free energy density in logarithmic radius. -/
def intervalEnergyDensity (F : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖deriv F x‖ ^ 2 + 4 * ‖F x‖ ^ 2

/-- Mode-two free energy on the actual interval. -/
def intervalEnergy (F : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ x in Ioc a b, intervalEnergyDensity F x

lemma contDiff_deriv_of_two {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (deriv F) :=
  (contDiff_succ_iff_deriv.mp hF).2.2

lemma continuous_second_of_two {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) :
    Continuous (deriv (deriv F)) :=
  (contDiff_deriv_of_two hF).continuous_deriv_one

lemma intervalEnergyDensity_continuous {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) :
    Continuous (intervalEnergyDensity F) :=
  ((hF.continuous_deriv (by norm_num)).norm.pow 2).add
    ((hF.continuous.norm.pow 2).const_mul 4)

lemma intervalEnergyDensity_integrable {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (a b : ℝ) : IntegrableOn (intervalEnergyDensity F) (Ioc a b) :=
  (intervalEnergyDensity_continuous hF).integrableOn_Ioc

lemma second_pairing_integrable {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (a b : ℝ) :
    IntegrableOn (fun x => conj (F x) * deriv (deriv F) x) (Ioc a b) :=
  (hF.continuous.star.mul (continuous_second_of_two hF)).integrableOn_Ioc

lemma dirichlet_pairing_integrable {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (a b : ℝ) :
    IntegrableOn (fun x => conj (F x) * (deriv (deriv F) x - 4 * F x)) (Ioc a b) :=
  (hF.continuous.star.mul
    ((continuous_second_of_two hF).sub (hF.continuous.const_mul 4))).integrableOn_Ioc

lemma freeResidual_norm_sq_integrable {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (a b : ℝ) :
    IntegrableOn (fun x => ‖deriv (deriv F) x - 4 * F x‖ ^ 2) (Ioc a b) :=
  (((continuous_second_of_two hF).sub (hF.continuous.const_mul 4)).norm.pow 2).integrableOn_Ioc

/-- The actual second derivative pairing, with the boundary term removed. -/
theorem integral_conj_mul_second_eq_neg {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    {a b : ℝ} (hab : a ≤ b) (ha : F a = 0) (hb : F b = 0) :
    (∫ x in Ioc a b, conj (F x) * deriv (deriv F) x) =
      -((∫ x in Ioc a b, ‖deriv F x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv F) :=
    (contDiff_deriv_of_two hF).differentiable (by norm_num)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x => conj (F x)) (v := deriv F)
    (u' := fun x => conj (deriv F x)) (v' := deriv (deriv F))
    (fun x _ => (hd x).hasDerivAt.star)
    (fun x _ => (hd' x).hasDerivAt)
    ((hF.continuous_deriv (by norm_num)).star.intervalIntegrable a b)
    ((continuous_second_of_two hF).intervalIntegrable a b)
  simp only [ha, hb, map_zero, zero_mul, sub_self, zero_sub,
    intervalIntegral.integral_of_le hab] at hi
  simp_rw [Complex.conj_mul', ← Complex.ofReal_pow] at hi
  rw [integral_complex_ofReal] at hi
  exact hi

/-- The complex pairing of the mode-two free differential expression is
exactly the negative real energy. -/
theorem integral_conj_mul_free_eq_neg_energy {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    {a b : ℝ} (hab : a ≤ b) (ha : F a = 0) (hb : F b = 0) :
    (∫ x in Ioc a b, conj (F x) * (deriv (deriv F) x - 4 * F x)) =
      -(intervalEnergy F a b : ℂ) := by
  have hFn : IntegrableOn (fun x => ‖F x‖ ^ 2) (Ioc a b) :=
    (hF.continuous.norm.pow 2).integrableOn_Ioc
  have hDn : IntegrableOn (fun x => ‖deriv F x‖ ^ 2) (Ioc a b) :=
    ((hF.continuous_deriv (by norm_num)).norm.pow 2).integrableOn_Ioc
  have hFc : IntegrableOn (fun x => (‖F x‖ ^ 2 : ℂ)) (Ioc a b) :=
    by simpa only [Function.comp_def, Pi.pow_apply, Complex.ofReal_pow] using
      (Complex.continuous_ofReal.comp (hF.continuous.norm.pow 2)).integrableOn_Ioc
        (a := a) (b := b) (μ := volume)
  have heq : (fun x => conj (F x) * (deriv (deriv F) x - 4 * F x)) =
      (fun x => conj (F x) * deriv (deriv F) x - 4 * (‖F x‖ ^ 2 : ℂ)) := by
    funext x
    rw [mul_sub]
    congr 1
    rw [mul_left_comm, Complex.conj_mul']
  rw [heq, integral_sub (second_pairing_integrable hF a b) (hFc.const_mul 4),
    integral_const_mul, integral_conj_mul_second_eq_neg hF hab ha hb]
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  unfold intervalEnergy intervalEnergyDensity
  rw [integral_add hDn (hFn.const_mul 4), integral_const_mul]
  push_cast
  ring

lemma intervalEnergy_nonneg (F : ℝ → ℂ) (a b : ℝ) :
    0 ≤ intervalEnergy F a b := by
  exact integral_nonneg (fun x => add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- The elementary mass lower bound is genuine because all finite-interval
energy terms are integrable. -/
theorem four_mass_le_intervalEnergy {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (a b : ℝ) :
    4 * (∫ x in Ioc a b, ‖F x‖ ^ 2) ≤ intervalEnergy F a b := by
  have hFn : IntegrableOn (fun x => ‖F x‖ ^ 2) (Ioc a b) :=
    (hF.continuous.norm.pow 2).integrableOn_Ioc
  have hDn : IntegrableOn (fun x => ‖deriv F x‖ ^ 2) (Ioc a b) :=
    ((hF.continuous_deriv (by norm_num)).norm.pow 2).integrableOn_Ioc
  unfold intervalEnergy intervalEnergyDensity
  rw [integral_add hDn (hFn.const_mul 4), integral_const_mul]
  have hn : 0 ≤ ∫ x in Ioc a b, ‖deriv F x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

/-- Normalized Dirichlet modes have free energy at least four. -/
theorem four_le_intervalEnergy_of_normalized {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    {a b : ℝ} (hmass : (∫ x in Ioc a b, ‖F x‖ ^ 2) = 1) :
    4 ≤ intervalEnergy F a b := by
  simpa only [hmass, mul_one] using four_mass_le_intervalEnergy hF a b

end UnforcedLeray.Rayleigh
