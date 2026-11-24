import UnforcedLeray.GaussianQuadratic
import UnforcedLeray.GaussianPotentialSup
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The admissible negative trial in logarithmic radius

This module transports the actual Gaussian radial trial to the real log-radius
line. It proves square integrability of the trial and its classical derivative,
the weak integration-by-parts identity against compactly supported C¹ tests,
and strict negativity of the actual log-radius quadratic integral. It makes no
spectral-existence or Navier–Stokes existence assertion.
-/

noncomputable section

namespace UnforcedLeray.GaussianLogTrial

open MeasureTheory Set GaussianTrial GaussianQuadratic

/-- The actual logarithmic trial, `F(t)=φ(exp t)`. -/
def logTrial (t : ℝ) : ℝ := radialTrial (Real.exp t)

theorem hasDerivAt_logTrial (t : ℝ) :
    HasDerivAt logTrial (deriv radialTrial (Real.exp t) * Real.exp t) t := by
  rw [deriv_radialTrial]
  exact (hasDerivAt_radialTrial (Real.exp t)).comp t (Real.hasDerivAt_exp t)

theorem deriv_logTrial (t : ℝ) :
    deriv logTrial t = deriv radialTrial (Real.exp t) * Real.exp t :=
  (hasDerivAt_logTrial t).deriv

theorem continuous_logTrial : Continuous logTrial := by
  unfold logTrial radialTrial
  fun_prop

theorem continuous_deriv_logTrial : Continuous (deriv logTrial) := by
  have he : deriv logTrial = fun t =>
      Real.exp t * (2 - (Real.exp t) ^ 2 / 4) *
        Real.exp (-((Real.exp t) ^ 2 / 8)) * Real.exp t := by
    funext t
    rw [deriv_logTrial, deriv_radialTrial]
  rw [he]
  fun_prop

/-- General integrability transport under the actual exponential Jacobian. -/
theorem integrable_exp_substitution (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0)) :
    Integrable (fun t => g (Real.exp t) * Real.exp t) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  have hi := h.mp hg
  simpa only [abs_of_pos (Real.exp_pos _), smul_eq_mul, mul_comm, integrableOn_univ] using hi

/-- Exact integral substitution `r=exp t`. -/
theorem integral_exp_substitution (g : ℝ → ℝ) :
    (∫ t : ℝ, g (Real.exp t) * Real.exp t) = ∫ r : ℝ in Ioi 0, g r := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  simpa only [abs_of_pos (Real.exp_pos _), smul_eq_mul, mul_comm, Measure.restrict_univ] using h.symm

private theorem radial_exp_square (r : ℝ) :
    Real.exp (-(r ^ 2 / 8)) ^ 2 = Real.exp (-(r ^ 2 / 4)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- The separate mass term under the square-radius substitution. -/
theorem radial_mass_substitution (r : ℝ) (hr : 0 < r) :
    radialTrial r ^ 2 / r =
      (8 * (squareRadius r * Real.exp (-squareRadius r))) * (r / 2) := by
  unfold radialTrial squareRadius
  rw [mul_pow, radial_exp_square]
  field_simp
  ring

/-- The transformed radial derivative term, independently of potential cancellation. -/
def transformedDerivativeSquare (x : ℝ) : ℝ :=
  8 * (x ^ 3 * Real.exp (-x)) - 32 * (x ^ 2 * Real.exp (-x)) +
    32 * (x * Real.exp (-x))

theorem radial_derivative_substitution (r : ℝ) :
    (deriv radialTrial r) ^ 2 * r =
      transformedDerivativeSquare (squareRadius r) * (r / 2) := by
  rw [deriv_radialTrial]
  unfold transformedDerivativeSquare squareRadius
  simp only [mul_pow, radial_exp_square]
  ring

theorem integrable_transformed_derivative : IntegrableOn transformedDerivativeSquare (Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa only [pow_one] using integrable_pow_exp_neg 1
  exact (((integrable_pow_exp_neg 3).const_mul 8).sub
    ((integrable_pow_exp_neg 2).const_mul 32)).add (h1.const_mul 32)

theorem integrable_radial_mass :
    IntegrableOn (fun r : ℝ => radialTrial r ^ 2 / r) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => 8 * (x * Real.exp (-x))) (Ioi 0) := by
    simpa only [pow_one, IntegrableOn] using (integrable_pow_exp_neg 1).const_mul 8
  apply (integrable_squareRadius_substitution _ hg).congr_fun _ measurableSet_Ioi
  intro r hr
  exact (radial_mass_substitution r hr).symm

theorem integrable_radial_derivative_square :
    IntegrableOn (fun r : ℝ => (deriv radialTrial r) ^ 2 * r) (Ioi 0) := by
  apply (integrable_squareRadius_substitution transformedDerivativeSquare
    integrable_transformed_derivative).congr_fun _ measurableSet_Ioi
  intro r _
  exact (radial_derivative_substitution r).symm

/-- Square integrability of the logarithmic trial. -/
theorem integrable_logTrial_square : Integrable (fun t : ℝ => logTrial t ^ 2) := by
  have h := integrable_exp_substitution _ integrable_radial_mass
  apply h.congr
  filter_upwards [] with t
  unfold logTrial
  field_simp

/-- Separate square integrability of its actual derivative. -/
theorem integrable_deriv_logTrial_square :
    Integrable (fun t : ℝ => (deriv logTrial t) ^ 2) := by
  have h := integrable_exp_substitution _ integrable_radial_derivative_square
  apply h.congr
  filter_upwards [] with t
  rw [deriv_logTrial]
  ring

/-- Exact squared `L²` mass of the trial, in logarithmic radius. -/
theorem integral_logTrial_square : (∫ t : ℝ, logTrial t ^ 2) = 8 := by
  calc
    (∫ t : ℝ, logTrial t ^ 2) =
        ∫ t : ℝ, (radialTrial (Real.exp t) ^ 2 / Real.exp t) * Real.exp t := by
          apply integral_congr_ae
          filter_upwards [] with t
          unfold logTrial
          field_simp
    _ = ∫ r : ℝ in Ioi 0, radialTrial r ^ 2 / r :=
      integral_exp_substitution (fun r => radialTrial r ^ 2 / r)
    _ = ∫ r : ℝ in Ioi 0,
        (8 * (squareRadius r * Real.exp (-squareRadius r))) * (r / 2) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          exact radial_mass_substitution
    _ = ∫ x : ℝ in Ioi 0, 8 * (x * Real.exp (-x)) :=
      integral_squareRadius_substitution (fun x => 8 * (x * Real.exp (-x)))
    _ = 8 := by
      rw [integral_const_mul]
      have h := integral_pow_exp_neg 1
      simp only [pow_one] at h
      rw [h]
      norm_num

/-- Exact squared `L²` mass of the classical derivative. -/
theorem integral_deriv_logTrial_square : (∫ t : ℝ, (deriv logTrial t) ^ 2) = 16 := by
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa only [pow_one] using integrable_pow_exp_neg 1
  have h32 : IntegrableOn
      (fun x : ℝ => 8 * (x ^ 3 * Real.exp (-x)) - 32 * (x ^ 2 * Real.exp (-x)))
      (Ioi 0) := ((integrable_pow_exp_neg 3).const_mul 8).sub
        ((integrable_pow_exp_neg 2).const_mul 32)
  calc
    (∫ t : ℝ, (deriv logTrial t) ^ 2) =
        ∫ t : ℝ, ((deriv radialTrial (Real.exp t)) ^ 2 * Real.exp t) * Real.exp t := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [deriv_logTrial]
          ring
    _ = ∫ r : ℝ in Ioi 0, (deriv radialTrial r) ^ 2 * r :=
      integral_exp_substitution (fun r => (deriv radialTrial r) ^ 2 * r)
    _ = ∫ r : ℝ in Ioi 0, transformedDerivativeSquare (squareRadius r) * (r / 2) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r _
          exact radial_derivative_substitution r
    _ = ∫ x : ℝ in Ioi 0, transformedDerivativeSquare x :=
      integral_squareRadius_substitution _
    _ = 16 := by
      unfold transformedDerivativeSquare
      rw [integral_add h32 (h1.const_mul 32),
        integral_sub ((integrable_pow_exp_neg 3).const_mul 8)
          ((integrable_pow_exp_neg 2).const_mul 32)]
      simp only [integral_const_mul, integral_pow_exp_neg]
      have h := integral_pow_exp_neg 1
      simp only [pow_one] at h
      rw [h]
      norm_num [Nat.factorial]

/-- The trial is pointwise positive, hence is not the zero trial. -/
theorem logTrial_pos (t : ℝ) : 0 < logTrial t := by
  unfold logTrial radialTrial
  positivity

/-- The trial belongs to the standard Mathlib `L²` predicate. -/
theorem logTrial_memLp_two : MemLp logTrial 2 volume :=
  (memLp_two_iff_integrable_sq continuous_logTrial.aestronglyMeasurable).2
    integrable_logTrial_square

/-- Its actual classical derivative also belongs to standard `L²`. -/
theorem deriv_logTrial_memLp_two : MemLp (deriv logTrial) 2 volume :=
  (memLp_two_iff_integrable_sq continuous_deriv_logTrial.aestronglyMeasurable).2
    integrable_deriv_logTrial_square

/-- The independently formalized potential is exactly the radial potential times `r²`. -/
theorem Wlog_eq_radial (t : ℝ) :
    GaussianPotential.Wlog t = (Real.exp t) ^ 2 * radialPotential (Real.exp t) := by
  have he : Real.exp (2 * t) = (Real.exp t) ^ 2 := by
    simpa using Real.exp_nat_mul t 2
  unfold GaussianPotential.Wlog GaussianPotential.W radialPotential squareRadius bernoulliRatio
  rw [he]
  by_cases h : (Real.exp t) ^ 2 / 4 - 2 = 0
  · simp only [h, ↓reduceIte, mul_one]
    linarith
  · simp only [h, ↓reduceIte]
    ring

/-- The original log-radius quadratic-form integrand. -/
def logEnergyIntegrand (t : ℝ) : ℝ :=
  (deriv logTrial t) ^ 2 + (4 - GaussianPotential.Wlog t) * logTrial t ^ 2

theorem log_energy_substitution_identity (t : ℝ) :
    logEnergyIntegrand t = radialEnergyIntegrand (Real.exp t) * Real.exp t := by
  unfold logEnergyIntegrand
  rw [deriv_logTrial, Wlog_eq_radial]
  unfold radialEnergyIntegrand logTrial
  field_simp
  ring

/-- Integrability of the actual log quadratic form. -/
theorem integrable_log_energy : Integrable logEnergyIntegrand := by
  have h := integrable_exp_substitution radialEnergyIntegrand integrable_radial_energy
  apply h.congr
  filter_upwards [] with t
  exact (log_energy_substitution_identity t).symm

/-- Actual log-radius quadratic integral, not an assumed transformation formula. -/
theorem integral_log_energy :
    (∫ t : ℝ, logEnergyIntegrand t) = 48 - 32 * actualTrialIntegral := by
  calc
    (∫ t : ℝ, logEnergyIntegrand t) =
        ∫ t : ℝ, radialEnergyIntegrand (Real.exp t) * Real.exp t := by
          apply integral_congr_ae
          filter_upwards [] with t
          exact log_energy_substitution_identity t
    _ = ∫ r : ℝ in Ioi 0, radialEnergyIntegrand r :=
      integral_exp_substitution radialEnergyIntegrand
    _ = 48 - 32 * actualTrialIntegral := integral_radial_energy

/-- Strict negativity for a genuine `L²` trial with `L²` derivative. -/
theorem log_trial_strictly_negative : (∫ t : ℝ, logEnergyIntegrand t) < 0 := by
  rw [integral_log_energy]
  exact actual_trial_expression_negative

/-- The standard weak-derivative identity against every compactly supported `C¹` test. -/
theorem logTrial_weak_derivative (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    (∫ t : ℝ, logTrial t * deriv ψ t) = - ∫ t : ℝ, deriv logTrial t * ψ t := by
  have htestderiv : Continuous (deriv ψ) := hψ.continuous_deriv_one
  have hprod1 : Integrable (logTrial * deriv ψ) :=
    (continuous_logTrial.mul htestderiv).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hprod2 : Integrable (deriv logTrial * ψ) :=
    (continuous_deriv_logTrial.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hprod : Integrable (logTrial * ψ) :=
    (continuous_logTrial.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t _ => (hasDerivAt_logTrial t).differentiableAt.hasDerivAt)
    (fun t _ => (hψ.differentiable (by norm_num) t).hasDerivAt)
    hprod1 hprod2 hprod

/-- Genuine `H¹` admissibility expressed using standard `MemLp` and weak tests. -/
theorem logTrial_h1_admissible :
    MemLp logTrial 2 volume ∧ MemLp (deriv logTrial) 2 volume ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ t : ℝ, logTrial t * deriv ψ t) = - ∫ t : ℝ, deriv logTrial t * ψ t :=
  ⟨logTrial_memLp_two, deriv_logTrial_memLp_two, logTrial_weak_derivative⟩

end UnforcedLeray.GaussianLogTrial
