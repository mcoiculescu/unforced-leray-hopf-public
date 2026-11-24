import UnforcedLeray.Analysis.Sturm.EigenfunctionWeakRegularity
import UnforcedLeray.Analysis.Sturm.NeutralCriticalSpeed

/-!
# Neutral-speed exclusion for the genuine weak Gaussian Rayleigh equation

The actual undivided equation at the neutral speed has a scalar factor that
vanishes at precisely one point. Cancelling it almost everywhere identifies
the genuine weak Gaussian Sturm equation. The checked weak neutral-kernel
exclusion then applies, without assuming a classical representative or a
critical-point value of the weak second derivative.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm GaussianPotential NonUniqueEuler.Sob

/-- Almost-everywhere cancellation of the actual neutral Gaussian factor. -/
theorem neutral_equation_ae_of_critical_rayleigh {u ddu : ℝ → ℂ}
    (heq : ∀ᵐ t ∂volume, ((neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ)) *
      (ddu t - 4 * u t) - (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    ∀ᵐ t ∂volume, -ddu t + (4 - (Wlog t : ℂ)) * u t = 0 := by
  filter_upwards [heq, (volume : Measure ℝ).ae_ne neutralCriticalTime] with t h ht
  have hb : (gaussianOffset t : ℂ) ≠ 0 := by
    exact_mod_cast gaussianOffset_ne_zero_of_ne_critical ht
  have hprod : (gaussianOffset t : ℂ) *
      (-ddu t + (4 - (Wlog t : ℂ)) * u t) = 0 := by
    simp only [gaussianRayleighCoefficient, gaussianOffset, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_sub] at h ⊢
    linear_combination -h
  exact (mul_eq_zero.mp hprod).resolve_left hb

/-- The undivided equation implies equality in the actual L² operator domain. -/
theorem weak_neutral_operator_eq_zero (u ddu : ComplexL2)
    (heq : ∀ᵐ t ∂volume, ((neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ)) *
      (ddu t - 4 * u t) - (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    -ddu + (4 : ℂ) • u - complexPotentialOperator u = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [neutral_equation_ae_of_critical_rayleigh heq,
    Lp.coeFn_neg ddu, Lp.coeFn_smul (4 : ℂ) u,
    Lp.coeFn_add (-ddu) ((4 : ℂ) • u),
    Lp.coeFn_sub (-ddu + (4 : ℂ) • u) (complexPotentialOperator u),
    coeFn_complexPotentialOperator u] with t he hn hm ha hs hp
  simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at *
  rw [hs, ha, hn, hm, hp]
  simpa only [Pi.zero_apply, sub_mul, add_sub_assoc] using he

/-- There is no nonzero genuine weak H² mode at the Gaussian neutral speed. -/
theorem weak_critical_rayleigh_eq_zero (u du ddu : ComplexL2)
    (h1 : HasWeakDerivOn univ (derivList 1) (u : ℝ → ℂ) (du : ℝ → ℂ))
    (h2 : HasWeakDerivOn univ (derivList 1) (du : ℝ → ℂ) (ddu : ℝ → ℂ))
    (heq : ∀ᵐ t ∂volume, ((neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ)) *
      (ddu t - 4 * u t) - (gaussianRayleighCoefficient t : ℂ) * u t = 0) : u = 0 := by
  by_contra hu
  apply not_nonempty_gaussianSturmEigenfunction_zero
  refine ⟨{
    value := u
    first := du
    second := ddu
    nonzero := hu
    weakFirst := h1
    weakSecond := h2
    equation := ?_ }⟩
  simpa only [Complex.ofReal_zero, zero_smul] using weak_neutral_operator_eq_zero u ddu heq

end UnforcedLeray.Rayleigh.RealSpeed
