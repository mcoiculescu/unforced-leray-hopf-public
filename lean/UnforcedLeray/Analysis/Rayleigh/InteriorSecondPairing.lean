import UnforcedLeray.Analysis.Rayleigh.WeakExtractionPairings

/-!
# Actual second-order pairings away from the annular boundary

Twice integrating by parts cancels the boundary terms using the mode's
Dirichlet traces and the test's vanishing endpoint values. This gives a
second-order identity only for these interior tests, not a global H²
assertion for the zero-extended annular function.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh

/-- Actual twice-IBP identity on the finite interval. -/
theorem integral_mul_second_eq_second_mul {F ψ : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hψ : ContDiff ℝ 2 ψ)
    {l r : ℝ} (hlr : l ≤ r) (hFl : F l = 0) (hFr : F r = 0)
    (hψl : ψ l = 0) (hψr : ψ r = 0) :
    (∫ t in Ioc l r, F t * deriv (deriv ψ) t) =
      ∫ t in Ioc l r, deriv (deriv F) t * ψ t := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFdd : Differentiable ℝ (deriv F) :=
    (contDiff_deriv_of_two hF).differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hψdd : Differentiable ℝ (deriv ψ) :=
    (contDiff_deriv_of_two hψ).differentiable (by norm_num)
  have hi₁ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := F) (v := deriv ψ) (u' := deriv F) (v' := deriv (deriv ψ))
    (fun t _ => (hFd t).hasDerivAt) (fun t _ => (hψdd t).hasDerivAt)
    ((hF.continuous_deriv (by norm_num)).intervalIntegrable l r)
    ((continuous_second_of_two hψ).intervalIntegrable l r)
  have hi₂ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := deriv F) (v := ψ) (u' := deriv (deriv F)) (v' := deriv ψ)
    (fun t _ => (hFdd t).hasDerivAt) (fun t _ => (hψd t).hasDerivAt)
    ((continuous_second_of_two hF).intervalIntegrable l r)
    ((hψ.continuous_deriv (by norm_num)).intervalIntegrable l r)
  simp only [hFl, hFr, zero_mul, sub_self, zero_sub,
    intervalIntegral.integral_of_le hlr] at hi₁
  simp only [hψl, hψr, mul_zero, sub_self, zero_sub,
    intervalIntegral.integral_of_le hlr] at hi₂
  rw [hi₁, hi₂, neg_neg]

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)
include h

/-- Interior tests identify the zero-extended residual with the actual
second derivative minus four times the field, with all boundary terms proved zero. -/
theorem zeroExtension_second_pairing {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hψl : ψ l = 0) (hψr : ψ r = 0) :
    (∫ t, zeroExtension l r F t * deriv (deriv ψ) t) =
      (∫ t, zeroExtension l r (fun x => deriv (deriv F) x - 4 * F x) t * ψ t) +
      4 * (∫ t, zeroExtension l r F t * ψ t) := by
  rw [integral_zeroExtension_mul, integral_zeroExtension_mul, integral_zeroExtension_mul,
    integral_mul_second_eq_second_mul h.regularity hψ h.ordered
      h.left_endpoint h.right_endpoint hψl hψr]
  have hi₁ : IntegrableOn (fun t => deriv (deriv F) t * ψ t) (Ioc l r) :=
    ((continuous_second_of_two h.regularity).mul hψ.continuous).integrableOn_Ioc
  have hi₂ : IntegrableOn (fun t => F t * ψ t) (Ioc l r) :=
    (h.regularity.continuous.mul hψ.continuous).integrableOn_Ioc
  have he : (fun t => (deriv (deriv F) t - 4 * F t) * ψ t) =
      (fun t => deriv (deriv F) t * ψ t - 4 * (F t * ψ t)) := by
    funext t
    ring
  rw [he, integral_sub hi₁ (hi₂.const_mul 4), integral_const_mul]
  ring

/-- The same actual identity for the guarded L² quotient classes. -/
theorem fieldL2_second_pairing {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (hψl : ψ l = 0) (hψr : ψ r = 0) :
    (∫ t, h.fieldL2 t * deriv (deriv ψ) t) =
      (∫ t, h.residualL2 t * ψ t) + 4 * (∫ t, h.fieldL2 t * ψ t) := by
  rw [h.integral_fieldL2_mul, h.integral_residualL2_mul, h.integral_fieldL2_mul]
  exact h.zeroExtension_second_pairing hψ hψl hψr

end ShiftedAnnularMode
end UnforcedLeray.Rayleigh
