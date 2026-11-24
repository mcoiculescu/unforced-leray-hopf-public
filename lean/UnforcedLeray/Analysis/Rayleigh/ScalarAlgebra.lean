import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Scalar identities for the actual complex Rayleigh coefficient

The spectral denominator is nonzero in the open upper half-plane. All identities
below concern the ordinary complex quotient; no energy or moment identity is
postulated. They supply the algebra used after the Rayleigh ODE is integrated.
-/

noncomputable section
namespace UnforcedLeray.Rayleigh

/-- Squared modulus of the shifted critical-layer denominator. -/
def denominator (b : ℝ) (z : ℂ) : ℝ := Complex.normSq ((b : ℂ) - z)

/-- The quotient occurring in the logarithmic Rayleigh equation. -/
def criticalRatio (b : ℝ) (z : ℂ) : ℂ := (b : ℂ) / ((b : ℂ) - z)

theorem denominator_eq (b : ℝ) (z : ℂ) :
    denominator b z = (b - z.re) ^ 2 + z.im ^ 2 := by
  simp [denominator, Complex.normSq_apply]
  ring

theorem denominator_nonneg (b : ℝ) (z : ℂ) : 0 ≤ denominator b z :=
  Complex.normSq_nonneg _

theorem criticalDenominator_ne_zero (b : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (b : ℂ) - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hi
  linarith

theorem denominator_pos (b : ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < denominator b z :=
  Complex.normSq_pos.mpr (criticalDenominator_ne_zero b hz)

theorem criticalRatio_re (b : ℝ) (z : ℂ) :
    (criticalRatio b z).re = b * (b - z.re) / denominator b z := by
  simp [criticalRatio, Complex.div_re, denominator]

theorem criticalRatio_im (b : ℝ) (z : ℂ) :
    (criticalRatio b z).im = b * z.im / denominator b z := by
  simp [criticalRatio, Complex.div_im, denominator]
  ring

theorem normSq_criticalRatio (b : ℝ) (z : ℂ) :
    Complex.normSq (criticalRatio b z) = b ^ 2 / denominator b z := by
  simp [criticalRatio, denominator, sq]

theorem norm_criticalRatio_sq (b : ℝ) (z : ℂ) :
    ‖criticalRatio b z‖ ^ 2 = b ^ 2 / denominator b z := by
  rw [← Complex.normSq_eq_norm_sq]
  exact normSq_criticalRatio b z

/-- The real part differs from the positive square coefficient by one moment term. -/
theorem criticalRatio_re_eq_square_sub (b : ℝ) (z : ℂ) :
    (criticalRatio b z).re =
      b ^ 2 / denominator b z - z.re * (b / denominator b z) := by
  rw [criticalRatio_re]
  ring

/-- The exact cancellation used to remove distance-to-real-axis denominators
from the final energy estimate. -/
theorem squareCoefficient_eq (b : ℝ) {z : ℂ} (hz : 0 < z.im) :
    b ^ 2 / denominator b z =
      1 - Complex.normSq z / denominator b z + 2 * z.re * (b / denominator b z) := by
  have hd := (denominator_pos b hz).ne'
  field_simp
  rw [denominator_eq, Complex.normSq_apply]
  ring

theorem denominator_im_sq_le (b : ℝ) (z : ℂ) : z.im ^ 2 ≤ denominator b z := by
  rw [denominator_eq]
  nlinarith [sq_nonneg (b - z.re)]

theorem continuous_denominator (b : ℝ → ℝ) (hb : Continuous b) (z : ℂ) :
    Continuous (fun t => denominator (b t) z) := by
  simpa only [denominator, Function.comp_def, Pi.sub_apply] using
    Complex.continuous_normSq.comp ((Complex.continuous_ofReal.comp hb).sub continuous_const)

theorem continuous_inv_denominator (b : ℝ → ℝ) (hb : Continuous b)
    {z : ℂ} (hz : 0 < z.im) : Continuous (fun t => (denominator (b t) z)⁻¹) :=
  (continuous_denominator b hb z).inv₀ (fun t => (denominator_pos (b t) hz).ne')

theorem continuous_criticalRatio (b : ℝ → ℝ) (hb : Continuous b)
    {z : ℂ} (hz : 0 < z.im) : Continuous (fun t => criticalRatio (b t) z) := by
  unfold criticalRatio
  exact (Complex.continuous_ofReal.comp hb).div
    ((Complex.continuous_ofReal.comp hb).sub continuous_const)
    (fun t => criticalDenominator_ne_zero (b t) hz)

/-- The full scalar coefficient in a complex energy pairing. -/
theorem weighted_pairing_re (w b : ℝ) (z F : ℂ) :
    (((w : ℂ) * criticalRatio b z) * (F * star F)).re =
      w * (b * (b - z.re) / denominator b z) * ‖F‖ ^ 2 := by
  rw [show F * star F = (Complex.normSq F : ℂ) from Complex.mul_conj F]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, zero_mul, criticalRatio_re, Complex.normSq_eq_norm_sq]

/-- The imaginary energy coefficient is the critical moment times Im z. -/
theorem weighted_pairing_im (w b : ℝ) (z F : ℂ) :
    (((w : ℂ) * criticalRatio b z) * (F * star F)).im =
      z.im * (w * b / denominator b z * ‖F‖ ^ 2) := by
  rw [show F * star F = (Complex.normSq F : ℂ) from Complex.mul_conj F]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, add_zero, zero_mul, criticalRatio_im, Complex.normSq_eq_norm_sq]
  ring

/-- Squared modulus of the actual Rayleigh forcing coefficient. -/
theorem forcing_norm_sq (w b : ℝ) (z F : ℂ) :
    ‖((w : ℂ) * criticalRatio b z) * F‖ ^ 2 =
      w ^ 2 * (b ^ 2 / denominator b z) * ‖F‖ ^ 2 := by
  rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_criticalRatio_sq]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]


end UnforcedLeray.Rayleigh
