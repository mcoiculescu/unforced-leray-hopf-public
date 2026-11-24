import UnforcedLeray.Analysis.Sturm.QuadraticForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Convergent Gaussian-weighted annular integrals

The potential is the actual completed Gaussian `Wlog`. Boundedness and
measurability give genuine integrability on finite intervals for its products
with continuous coefficient functions; no divergent integral is used.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm

variable {l r : ℝ}

theorem integrableOn_Wlog_mul {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn (fun t => Wlog t * g t) (Ioc l r) := by
  exact (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self).bdd_mul
    measurable_Wlog.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall norm_Wlog_le_eight)

theorem integrableOn_complex_Wlog_mul {g : ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn (fun t => (Wlog t : ℂ) * g t) (Ioc l r) := by
  apply (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self).bdd_mul
    (Complex.continuous_ofReal.measurable.comp measurable_Wlog).aestronglyMeasurable.restrict
  exact (show ∀ᵐ t ∂(volume.restrict (Ioc l r)), ‖(Complex.ofReal ∘ Wlog) t‖ ≤ 8 from
    Filter.Eventually.of_forall fun t => by
      simpa only [Function.comp_apply, Complex.norm_real] using norm_Wlog_le_eight t)

theorem integral_Wlog_norm_sq_nonneg (F : ℝ → ℂ) :
    0 ≤ ∫ t in Ioc l r, Wlog t * ‖F t‖ ^ 2 :=
  integral_nonneg fun t => mul_nonneg (Wlog_pos t).le (sq_nonneg _)

theorem integral_Wlog_norm_sq_le {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in Ioc l r, Wlog t * ‖F t‖ ^ 2) ≤
      8 * ∫ t in Ioc l r, ‖F t‖ ^ 2 := by
  rw [← integral_const_mul]
  exact integral_mono (integrableOn_Wlog_mul (hF.norm.pow 2))
    (((hF.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul 8)
    (fun t => mul_le_mul_of_nonneg_right (Wlog_le_eight t) (sq_nonneg _))

end UnforcedLeray.Rayleigh
