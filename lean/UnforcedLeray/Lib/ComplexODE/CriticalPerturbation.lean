import UnforcedLeray.Lib.ComplexODE.QuantitativeL1

/-!
# Exact perturbation identity around the completed neutral equation (copy of a draft; O4 input)

Copy, for compilation inside `Lib/ComplexODE`, of the uncompiled draft

(2026-10-26), which is not edited. Its lemma `rayleighPotential_sub_neutral` is already in
`Lib/ComplexODE/QuantitativeL1.lean` and is not repeated. Scoping note

(bypass B8 (ii)); blueprint unit B0034 (`paper/main.tex` lines 1011--1021).

`evansFunction_critical_perturbation`: at a neutral Dirichlet zero `N(b) = 0`,
`D(β, c) N'(b) = (α² - β²) ∫ N F + (c - a_*) ∫ W N F/(Ω - c)`.
-/

set_option autoImplicit false

noncomputable section
open Set
namespace UnforcedLeray.Rayleigh.Evans
open Sturm GaussianPotential

/-- The spectral perturbation is an actual Cauchy integral of the two actual
solutions. A neutral endpoint zero is used only as an intermediate hypothesis. -/
theorem evansFunction_critical_perturbation (α β a b : ℝ) {c : ℂ}
    (hc : 0 < c.im) (hb : neutralEvansFunction α a b = 0) :
    evansFunction β a b c * neutralNormalizedDerivative α a b =
      ((α : ℂ) ^ 2 - (β : ℂ) ^ 2) *
        (∫ t in a..b, neutralNormalizedF α a t * normalizedF β a c t) +
      (c - (gaussianCriticalSpeed : ℂ)) *
        (∫ t in a..b, (Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
          ((neutralOmega t : ℂ) - c)) := by
  have hN := (neutralNormalizedF_smooth α a).continuous
  have hF := (normalizedF_smooth β a hc).continuous
  have hΩ : Continuous (fun t => (neutralOmega t : ℂ) - c) :=
    (Complex.continuous_ofReal.comp continuous_neutralOmega).sub continuous_const
  have hW : Continuous (fun t => (Wlog t : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_Wlog
  have hI : IntervalIntegrable
      (fun t => neutralNormalizedF α a t * normalizedF β a c t)
      MeasureTheory.volume a b := (hN.mul hF).intervalIntegrable a b
  have hJ : IntervalIntegrable
      (fun t => (Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
        ((neutralOmega t : ℂ) - c)) MeasureTheory.volume a b :=
    (((hW.mul hN).mul hF).div hΩ (fun t => rayleigh_denominator_ne_zero hc t)).intervalIntegrable a b
  rw [evansFunction_mul_neutralDerivative α β a b hc hb]
  have hid : (fun t => (rayleighPotential β t c - neutralPotential α t) *
      neutralNormalizedF α a t * normalizedF β a c t) =
      (fun t => ((β : ℂ) ^ 2 - (α : ℂ) ^ 2) *
          (neutralNormalizedF α a t * normalizedF β a c t) -
        (c - (gaussianCriticalSpeed : ℂ)) *
          ((Wlog t : ℂ) * neutralNormalizedF α a t * normalizedF β a c t /
            ((neutralOmega t : ℂ) - c))) := by
    funext t
    rw [rayleighPotential_sub_neutral α β t hc]
    ring
  rw [hid, intervalIntegral.integral_sub (hI.const_mul _) (hJ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

end UnforcedLeray.Rayleigh.Evans
