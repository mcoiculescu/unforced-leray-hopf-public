import UnforcedLeray.Analysis.Rayleigh.WeightedIntegrals
import UnforcedLeray.Analysis.Rayleigh.ScalarAlgebra
import UnforcedLeray.Analysis.Rayleigh.IntervalEnergy

/-!
# Uniform estimates from the actual annular Rayleigh ODE

The hypotheses specify the actual differential equation, C² regularity and
Dirichlet boundary values on a finite interval. The energy and imaginary
moment identities are conclusions obtained by integration by parts. The
potential is the concrete Gaussian `Wlog`; it is not an abstract bounded input.
Existence of an unstable annular mode is a separate construction.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm

/-- The shifted logarithmic Rayleigh boundary problem, with the actual Gaussian
potential. For the physical mode, q=Ω−a* and z=c−a*. -/
structure ShiftedAnnularMode (q : ℝ → ℝ) (z : ℂ) (F : ℝ → ℂ) (l r : ℝ) : Prop where
  ordered : l ≤ r
  offset_continuous : Continuous q
  upper_half_plane : 0 < z.im
  regularity : ContDiff ℝ 2 F
  left_endpoint : F l = 0
  right_endpoint : F r = 0
  equation : ∀ t ∈ Ioc l r,
    deriv (deriv F) t - 4 * F t =
      -((Wlog t : ℂ) * criticalRatio (q t) z) * F t

def rayleighPairing (q : ℝ → ℝ) (z : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((Wlog t : ℂ) * criticalRatio (q t) z) * (F t * star (F t))

namespace ShiftedAnnularMode
variable {q : ℝ → ℝ} {z : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : ShiftedAnnularMode q z F l r)
include h

lemma pairing_integrable : IntegrableOn (rayleighPairing q z F) (Ioc l r) := by
  have hc := (continuous_criticalRatio q h.offset_continuous h.upper_half_plane).mul
    (h.regularity.continuous.mul h.regularity.continuous.star)
  convert integrableOn_complex_Wlog_mul (l := l) (r := r) hc using 1
  ext t
  simp only [rayleighPairing, Pi.mul_apply]
  ring

lemma moment_integrable : IntegrableOn
    (fun t => Wlog t * q t / denominator (q t) z * ‖F t‖ ^ 2) (Ioc l r) := by
  have hc := (h.offset_continuous.mul
    (continuous_inv_denominator q h.offset_continuous h.upper_half_plane)).mul
      (h.regularity.continuous.norm.pow 2)
  convert integrableOn_Wlog_mul (l := l) (r := r) hc using 1
  ext t
  simp only [div_eq_mul_inv, Pi.mul_apply, Pi.pow_apply]
  ring

lemma square_coefficient_integrable : IntegrableOn
    (fun t => Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2) (Ioc l r) := by
  have hc := ((h.offset_continuous.pow 2).mul
    (continuous_inv_denominator q h.offset_continuous h.upper_half_plane)).mul
      (h.regularity.continuous.norm.pow 2)
  convert integrableOn_Wlog_mul (l := l) (r := r) hc using 1
  ext t
  simp only [div_eq_mul_inv, Pi.mul_apply, Pi.pow_apply]
  ring

lemma denominator_coefficient_integrable : IntegrableOn
    (fun t => Wlog t / denominator (q t) z * ‖F t‖ ^ 2) (Ioc l r) := by
  have hc := (continuous_inv_denominator q h.offset_continuous h.upper_half_plane).mul
    (h.regularity.continuous.norm.pow 2)
  convert integrableOn_Wlog_mul (l := l) (r := r) hc using 1
  ext t
  simp only [div_eq_mul_inv, Pi.mul_apply, Pi.pow_apply]
  ring

/-- Integration of the actual ODE and removal of the genuine Dirichlet boundary term. -/
theorem complex_energy_identity :
    (intervalEnergy F l r : ℂ) = ∫ t in Ioc l r, rayleighPairing q z F t := by
  have hibp := integral_conj_mul_free_eq_neg_energy h.regularity h.ordered
    h.left_endpoint h.right_endpoint
  have heq : (∫ t in Ioc l r, conj (F t) * (deriv (deriv F) t - 4 * F t)) =
      -(∫ t in Ioc l r, rayleighPairing q z F t) := by
    calc
      _ = ∫ t in Ioc l r, -(rayleighPairing q z F t) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp only
        rw [h.equation t ht]
        simp only [rayleighPairing, starRingEnd_apply]
        ring
      _ = _ := integral_neg _
  exact neg_injective (hibp.symm.trans heq)

/-- The critical moment vanishes because the speed has strictly positive imaginary part. -/
theorem imaginary_moment_zero :
    (∫ t in Ioc l r, Wlog t * q t / denominator (q t) z * ‖F t‖ ^ 2) = 0 := by
  have him := congrArg Complex.im h.complex_energy_identity
  simp only [Complex.ofReal_im] at him
  have hcomm := integral_im h.pairing_integrable
  change (∫ t in Ioc l r, (rayleighPairing q z F t).im) =
    (∫ t in Ioc l r, rayleighPairing q z F t).im at hcomm
  rw [← hcomm] at him
  simp only [rayleighPairing, weighted_pairing_im] at him
  rw [integral_const_mul] at him
  exact (mul_eq_zero.mp him.symm).resolve_left h.upper_half_plane.ne'

/-- The actual energy equals a manifestly nonnegative rational integral. -/
theorem energy_eq_square_coefficient :
    intervalEnergy F l r =
      ∫ t in Ioc l r, Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2 := by
  have hre := congrArg Complex.re h.complex_energy_identity
  simp only [Complex.ofReal_re] at hre
  have hcomm := integral_re h.pairing_integrable
  change (∫ t in Ioc l r, (rayleighPairing q z F t).re) =
    (∫ t in Ioc l r, rayleighPairing q z F t).re at hcomm
  rw [← hcomm] at hre
  simp only [rayleighPairing, weighted_pairing_re] at hre
  have heq : (fun t => Wlog t * (q t * (q t - z.re) / denominator (q t) z) * ‖F t‖ ^ 2) =
      (fun t => Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2 -
        z.re * (Wlog t * q t / denominator (q t) z * ‖F t‖ ^ 2)) := by
    funext t
    ring
  rw [heq, integral_sub h.square_coefficient_integrable
    (h.moment_integrable.const_mul z.re), integral_const_mul, h.imaginary_moment_zero,
    mul_zero, sub_zero] at hre
  exact hre

/-- The cancellation identity removes the critical-layer denominator from the
upper energy bound, uniformly as the imaginary speed approaches zero. -/
theorem energy_eq_potential_sub :
    intervalEnergy F l r = (∫ t in Ioc l r, Wlog t * ‖F t‖ ^ 2) -
      Complex.normSq z * (∫ t in Ioc l r, Wlog t / denominator (q t) z * ‖F t‖ ^ 2) := by
  rw [h.energy_eq_square_coefficient]
  have heq : (fun t => Wlog t * (q t ^ 2 / denominator (q t) z) * ‖F t‖ ^ 2) =
      (fun t => (Wlog t * ‖F t‖ ^ 2 -
        Complex.normSq z * (Wlog t / denominator (q t) z * ‖F t‖ ^ 2)) +
        (2 * z.re) * (Wlog t * q t / denominator (q t) z * ‖F t‖ ^ 2)) := by
    funext t
    rw [squareCoefficient_eq (q t) h.upper_half_plane]
    ring
  have hW : IntegrableOn (fun t => Wlog t * ‖F t‖ ^ 2) (Ioc l r) :=
    integrableOn_Wlog_mul (h.regularity.continuous.norm.pow 2)
  have hD : IntegrableOn
      (fun t => Complex.normSq z * (Wlog t / denominator (q t) z * ‖F t‖ ^ 2))
      (Ioc l r) := h.denominator_coefficient_integrable.const_mul (Complex.normSq z)
  have hM : IntegrableOn
      (fun t => (2 * z.re) * (Wlog t * q t / denominator (q t) z * ‖F t‖ ^ 2))
      (Ioc l r) := h.moment_integrable.const_mul (2 * z.re)
  rw [heq, integral_add (hW.fun_sub hD) hM, integral_sub hW hD,
    integral_const_mul, integral_const_mul, h.imaginary_moment_zero, mul_zero, add_zero]

theorem energy_le_potential :
    intervalEnergy F l r ≤ ∫ t in Ioc l r, Wlog t * ‖F t‖ ^ 2 := by
  rw [h.energy_eq_potential_sub]
  apply sub_le_self
  apply mul_nonneg (Complex.normSq_nonneg z)
  exact integral_nonneg fun t => mul_nonneg
    (div_nonneg (Wlog_pos t).le (denominator_nonneg (q t) z)) (sq_nonneg _)

/-- The norm-one mode has uniform free energy between four and eight. -/
theorem normalized_energy_bounds
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    4 ≤ intervalEnergy F l r ∧ intervalEnergy F l r ≤ 8 := by
  have hlo := four_mass_le_intervalEnergy h.regularity l r
  have hhi := h.energy_le_potential.trans (integral_Wlog_norm_sq_le h.regularity.continuous)
  rw [hmass, mul_one] at hlo hhi
  exact ⟨hlo, hhi⟩

end ShiftedAnnularMode
end UnforcedLeray.Rayleigh
