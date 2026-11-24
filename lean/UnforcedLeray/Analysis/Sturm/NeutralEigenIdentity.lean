import UnforcedLeray.Analysis.Sturm.QuadraticForm
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Actual Sturm energy and cross identities

These identities use the concrete Gaussian potential, actual classical
second derivatives, and convergent whole-line Lebesgue integrals.
No selfadjointness or integration-by-parts identity is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace UnforcedLeray.Sturm
open GaussianPotential

/-- The actual real symmetric bilinear form associated with the Gaussian Sturm form. -/
def sturmBilinearForm (n : ℝ) (f f' g g' : ℝ → ℝ) : ℝ :=
  ∫ t, f' t * g' t + (n ^ 2 - Wlog t) * (f t * g t)

theorem integrable_sturmBilinear {f f' g g' : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hf' : MemLp f' 2 volume)
    (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume) (n : ℝ) :
    Integrable (fun t => f' t * g' t + (n ^ 2 - Wlog t) * (f t * g t)) := by
  have hfg : Integrable (fun t => f t * g t) := hf.integrable_mul hg
  have hd : Integrable (fun t => f' t * g' t) := hf'.integrable_mul hg'
  have hv : Integrable (fun t => Wlog t * (f t * g t)) :=
    hfg.bdd_mul measurable_Wlog.aestronglyMeasurable
      (Filter.Eventually.of_forall norm_Wlog_le_eight)
  simpa only [Pi.sub_def, Pi.add_def, sub_mul, ← add_sub_assoc] using
    (hd.add (hfg.const_mul (n ^ 2))).sub hv

theorem sturmBilinear_symm (n : ℝ) (f f' g g' : ℝ → ℝ) :
    sturmBilinearForm n f f' g g' = sturmBilinearForm n g g' f f' := by
  unfold sturmBilinearForm
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem sturmBilinear_self (n : ℝ) (f f' : ℝ → ℝ) :
    sturmBilinearForm n f f' f f' = quadraticForm n f f' := by
  simp only [sturmBilinearForm, quadraticForm, pow_two]

/-- Boundedness of the concrete potential supplies the second-derivative L²
condition from the eigen-equation and L² value alone. -/
theorem sturm_eigen_second_memLp {f : ℝ → ℝ} {n ev : ℝ}
    (hf : MemLp f 2 volume)
    (heq : ∀ t, -deriv (deriv f) t + (n ^ 2 - Wlog t) * f t = ev * f t) :
    MemLp (deriv (deriv f)) 2 volume := by
  have hw : MemLp (fun t => Wlog t * f t) 2 volume := by
    refine hf.of_le_mul (c := 8)
      (measurable_Wlog.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
    filter_upwards [] with t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_Wlog_le_eight t) (norm_nonneg _)
  have he : deriv (deriv f) = fun t => (n ^ 2 - ev) * f t - Wlog t * f t := by
    funext t
    have h := heq t
    nlinarith [h]
  rw [he]
  exact (hf.const_mul (n ^ 2 - ev)).sub hw

/-- Whole-line integration by parts without a boundary term, from actual L² data. -/
theorem integral_second_mul_eq_neg_first_mul {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hf1 : MemLp (deriv f) 2 volume) (hf2 : MemLp (deriv (deriv f)) 2 volume)
    (hg0 : MemLp g 2 volume) (hg1 : MemLp (deriv g) 2 volume) :
    (∫ t, deriv (deriv f) t * g t) = -(∫ t, deriv f t * deriv g t) := by
  have hi : (∫ t, deriv f t * deriv g t) = -(∫ t, deriv (deriv f) t * g t) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ => (hf.differentiable_deriv_two t).hasDerivAt)
      (fun t _ => (hg.differentiable (by norm_num) t).hasDerivAt)
      (hf1.integrable_mul hg1) (hf2.integrable_mul hg0) (hf1.integrable_mul hg0)
  linarith

/-- Testing the actual eigen-equation against any C¹ H¹ function gives this
identity, even when the test is not compactly supported. -/
theorem sturm_eigen_bilinear {f g : ℝ → ℝ} {n ev : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hf0 : MemLp f 2 volume) (hf1 : MemLp (deriv f) 2 volume)
    (hf2 : MemLp (deriv (deriv f)) 2 volume)
    (hg0 : MemLp g 2 volume) (hg1 : MemLp (deriv g) 2 volume)
    (heq : ∀ t, -deriv (deriv f) t + (n ^ 2 - Wlog t) * f t = ev * f t) :
    sturmBilinearForm n f (deriv f) g (deriv g) = ev * (∫ t, f t * g t) := by
  have hfg : Integrable (fun t => f t * g t) := hf0.integrable_mul hg0
  have hdg : Integrable (fun t => deriv f t * deriv g t) := hf1.integrable_mul hg1
  have hddg : Integrable (fun t => deriv (deriv f) t * g t) := hf2.integrable_mul hg0
  have hiv : Integrable (fun t => (n ^ 2 - Wlog t) * (f t * g t)) := by
    simpa only [Pi.sub_def, sub_mul] using (hfg.const_mul (n ^ 2)).sub
      (hfg.bdd_mul measurable_Wlog.aestronglyMeasurable
        (Filter.Eventually.of_forall norm_Wlog_le_eight))
  have hip : (∫ t, deriv (deriv f) t * g t) = -(∫ t, deriv f t * deriv g t) :=
    integral_second_mul_eq_neg_first_mul hf hg hf1 hf2 hg0 hg1
  have hpoint (t : ℝ) :
      - (deriv (deriv f) t * g t) + (n ^ 2 - Wlog t) * (f t * g t) =
        ev * (f t * g t) := by
    have h := congrArg (fun x : ℝ => x * g t) (heq t)
    nlinarith [h]
  have hint : (∫ t : ℝ, -(deriv (deriv f) t * g t) +
      (n ^ 2 - Wlog t) * (f t * g t)) = ∫ t : ℝ, ev * (f t * g t) :=
    integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hneg : Integrable (fun t => -(deriv (deriv f) t * g t)) := by
    simpa only [Pi.neg_def] using hddg.neg
  rw [integral_add hneg hiv, integral_neg, integral_const_mul, hip] at hint
  unfold sturmBilinearForm
  rw [integral_add hdg hiv]
  simpa only [neg_neg] using hint

/-- Eigenvalue times the actual mass equals the quadratic energy. -/
theorem sturm_eigen_energy {f : ℝ → ℝ} {n ev : ℝ}
    (hf : ContDiff ℝ 2 f) (hf0 : MemLp f 2 volume)
    (hf1 : MemLp (deriv f) 2 volume) (hf2 : MemLp (deriv (deriv f)) 2 volume)
    (heq : ∀ t, -deriv (deriv f) t + (n ^ 2 - Wlog t) * f t = ev * f t) :
    quadraticForm n f (deriv f) = ev * (∫ t, f t ^ 2) := by
  simpa only [sturmBilinear_self, pow_two] using
    sturm_eigen_bilinear hf (hf.of_le (by norm_num)) hf0 hf1 hf2 hf0 hf1 heq

end UnforcedLeray.Sturm
