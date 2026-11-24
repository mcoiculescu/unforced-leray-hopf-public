import UnforcedLeray.Analysis.Rayleigh.IntervalEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Actual one-dimensional H¹ Hölder bound on an interval

The fundamental theorem of calculus and Cauchy--Schwarz control pointwise
oscillation by the genuine square integral of the derivative.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace UnforcedLeray.Rayleigh

lemma integral_norm_le_sqrt_length {g : ℝ → ℂ} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Ioc a b, ‖g x‖) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ x in Ioc a b, ‖g x‖ ^ 2) := by
  have hg2 : MemLp (fun x => ‖g x‖) 2 (volume.restrict (Ioc a b)) := by
    have hc : Continuous (fun x => ‖g x‖ ^ 2) := hg.norm.pow 2
    have hi : Integrable (fun x => ‖g x‖ ^ 2) (volume.restrict (Ioc a b)) :=
      hc.integrableOn_Ioc
    have hmem : MemLp g 2 (volume.restrict (Ioc a b)) :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable.restrict).mpr hi
    exact hmem.norm
  have hc2 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioc a b)) :=
    memLp_const 1
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hi := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Filter.Eventually.of_forall (fun _ : ℝ => show 0 ≤ (1 : ℝ) by norm_num))
    (Filter.Eventually.of_forall (fun x : ℝ => norm_nonneg (g x)))
    (by simpa using hc2) (by simpa using hg2)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two, measureReal_def,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hi

lemma norm_integral_le_sqrt_length {g : ℝ → ℂ} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    ‖∫ x in Ioc a b, g x‖ ≤
      Real.sqrt (b - a) * Real.sqrt (∫ x in Ioc a b, ‖g x‖ ^ 2) :=
  (norm_integral_le_integral_norm _).trans (integral_norm_le_sqrt_length hg hab)

/-- Interior oscillation is controlled by the actual derivative square mass. -/
theorem norm_sub_le_sqrt_derivative_mass {F : ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    {a b : ℝ} (hab : a ≤ b) :
    ‖F b - F a‖ ≤
      Real.sqrt (b - a) * Real.sqrt (∫ x in Ioc a b, ‖deriv F x‖ ^ 2) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hc : Continuous (deriv F) := hF.continuous_deriv_one
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hd x) (hc.intervalIntegrable a b)
  rw [intervalIntegral.integral_of_le hab] at hFTC
  rw [← hFTC]
  exact norm_integral_le_sqrt_length hc hab

end UnforcedLeray.Rayleigh
