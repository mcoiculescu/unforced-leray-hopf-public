import UnforcedLeray.Analysis.Rayleigh.IntervalEnergy
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine weighted Dirichlet energy for the semicircle transformation

Integration of the derivative of `conj G * (H²G')` gives the complex weighted
energy identity. The differential equation is assumed pointwise on the actual
finite interval, while every integral and the vanishing boundary term are
proved. No energy or moment identity is used as a premise.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace UnforcedLeray.Rayleigh

/-- The nonnegative density in the mode-two ground-state transform. -/
def semicircleEnergyDensity (G : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖deriv G t‖ ^ 2 + 3 * ‖G t‖ ^ 2

theorem semicircleEnergyDensity_nonneg (G : ℝ → ℂ) (t : ℝ) :
    0 ≤ semicircleEnergyDensity G t :=
  add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))

theorem semicircleEnergyDensity_continuous {G : ℝ → ℂ} (hG : ContDiff ℝ 2 G) :
    Continuous (semicircleEnergyDensity G) :=
  ((hG.continuous_deriv (by norm_num)).norm.pow 2).add
    ((hG.continuous.norm.pow 2).const_mul 3)

theorem semicircleEnergyDensity_integrable {G : ℝ → ℂ} (hG : ContDiff ℝ 2 G)
    (a b : ℝ) : IntegrableOn (semicircleEnergyDensity G) (Ioc a b) :=
  (semicircleEnergyDensity_continuous hG).integrableOn_Ioc

theorem weighted_semicircleEnergy_integrable {H G : ℝ → ℂ}
    (hH : Continuous H) (hG : ContDiff ℝ 2 G) (a b : ℝ) :
    IntegrableOn (fun t => H t ^ 2 * (semicircleEnergyDensity G t : ℂ)) (Ioc a b) := by
  exact ((hH.pow 2).mul
    (Complex.continuous_ofReal.comp (semicircleEnergyDensity_continuous hG))).integrableOn_Ioc

/-- Actual complex weighted energy identity for a Dirichlet transformed mode. -/
theorem weighted_dirichlet_energy_zero {H G : ℝ → ℂ}
    (hH : ContDiff ℝ 2 H) (hG : ContDiff ℝ 2 G)
    {a b : ℝ} (hab : a ≤ b) (ha : G a = 0) (hb : G b = 0)
    (hode : ∀ t ∈ Ioc a b,
      deriv (fun x => H x ^ 2 * deriv G x) t = 3 * H t ^ 2 * G t) :
    (∫ t in Ioc a b, H t ^ 2 * (semicircleEnergyDensity G t : ℂ)) = 0 := by
  let J : ℝ → ℂ := fun x => H x ^ 2 * deriv G x
  have hH1 : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  have hJ : ContDiff ℝ 1 J := (hH1.pow 2).mul (contDiff_deriv_of_two hG)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hJd : Differentiable ℝ J := hJ.differentiable (by norm_num)
  have hi := intervalIntegral.integral_deriv_mul_eq_sub
    (u := fun t => conj (G t)) (v := J)
    (u' := fun t => conj (deriv G t)) (v' := deriv J)
    (fun t _ => (hGd t).hasDerivAt.star)
    (fun t _ => (hJd t).hasDerivAt)
    ((hG.continuous_deriv (by norm_num)).star.intervalIntegrable a b)
    (hJ.continuous_deriv_one.intervalIntegrable a b)
  simp only [ha, hb, map_zero, zero_mul, sub_self,
    intervalIntegral.integral_of_le hab] at hi
  calc
    (∫ t in Ioc a b, H t ^ 2 * (semicircleEnergyDensity G t : ℂ)) =
        ∫ t in Ioc a b, conj (deriv G t) * J t + conj (G t) * deriv J t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      have he : deriv J t = 3 * H t ^ 2 * G t := hode t ht
      rw [he]
      simp only [J, semicircleEnergyDensity, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_ofNat, Complex.ofReal_pow]
      have h1 : conj (deriv G t) * deriv G t = (‖deriv G t‖ : ℂ) ^ 2 :=
        Complex.conj_mul' _
      have h2 : conj (G t) * G t = (‖G t‖ : ℂ) ^ 2 := Complex.conj_mul' _
      linear_combination -(H t ^ 2) * h1 - (3 * H t ^ 2) * h2
    _ = 0 := hi

end UnforcedLeray.Rayleigh
