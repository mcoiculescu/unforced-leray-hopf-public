import UnforcedLeray.GaussianTrial
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The actual radial negative trial

The trial is `φ(r) = r² exp(-r²/8)` and the potential is the continuously
completed Gaussian potential from the manuscript. This module identifies its
radial quadratic-form integral by an actual change of variables `x = r²/4`.
It does not assert a spectral theorem or a Navier–Stokes existence result.
-/

noncomputable section

namespace UnforcedLeray.GaussianQuadratic

open MeasureTheory Set GaussianTrial

/-- Gaussian radial trial function in the manuscript. -/
def radialTrial (r : ℝ) : ℝ := r ^ 2 * Real.exp (-(r ^ 2 / 8))

/-- The radius substitution used in the trial calculation. -/
def squareRadius (r : ℝ) : ℝ := r ^ 2 / 4

/-- The positive potential with its removable value explicitly filled. -/
def radialPotential (r : ℝ) : ℝ := bernoulliRatio (squareRadius r - 2)

/-- The actual derivative of the trial, with no supplied derivative assumption. -/
theorem hasDerivAt_radialTrial (r : ℝ) :
    HasDerivAt radialTrial
      (r * (2 - r ^ 2 / 4) * Real.exp (-(r ^ 2 / 8))) r := by
  unfold radialTrial
  convert ((hasDerivAt_id r).pow 2).mul
    ((((hasDerivAt_id r).pow 2).div_const 8).neg.exp) using 1 <;>
    first | rfl | (dsimp; ring)

theorem deriv_radialTrial (r : ℝ) :
    deriv radialTrial r = r * (2 - r ^ 2 / 4) * Real.exp (-(r ^ 2 / 8)) :=
  (hasDerivAt_radialTrial r).deriv

theorem hasDerivAt_squareRadius (r : ℝ) : HasDerivAt squareRadius (r / 2) r := by
  unfold squareRadius
  convert ((hasDerivAt_id r).pow 2).div_const 4 using 1 <;>
    first | rfl | (dsimp; ring)

theorem squareRadius_injOn : InjOn squareRadius (Ioi 0) := by
  intro r hr s hs he
  apply (sq_eq_sq₀ (le_of_lt hr) (le_of_lt hs)).mp
  dsimp [squareRadius] at he
  linarith

theorem squareRadius_image : squareRadius '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change (0 : ℝ) < r ^ 2 / 4
    have hr0 : (0 : ℝ) < r := hr
    positivity
  · intro hx
    refine ⟨2 * Real.sqrt x, mul_pos (by norm_num) (Real.sqrt_pos.2 hx), ?_⟩
    dsimp [squareRadius]
    rw [mul_pow, Real.sq_sqrt (le_of_lt hx)]
    ring

/-- Jacobian substitution, including integrability transport. -/
theorem integrable_squareRadius_substitution (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun r => g (squareRadius r) * (r / 2)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (hasDerivAt_squareRadius r).hasDerivWithinAt) squareRadius_injOn g
  rw [squareRadius_image] at h
  apply (h.mp hg).congr_fun _ measurableSet_Ioi
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  have hr2 : (0 : ℝ) ≤ r / 2 := by positivity
  simp only [smul_eq_mul, abs_of_nonneg hr2]
  ring

/-- The exact integral substitution `x=r²/4`, with Jacobian `r/2`. -/
theorem integral_squareRadius_substitution (g : ℝ → ℝ) :
    (∫ r : ℝ in Ioi 0, g (squareRadius r) * (r / 2)) = ∫ x : ℝ in Ioi 0, g x := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (hasDerivAt_squareRadius r).hasDerivWithinAt) squareRadius_injOn g
  rw [squareRadius_image] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr0 : (0 : ℝ) < r := hr
  have hr2 : (0 : ℝ) ≤ r / 2 := by positivity
  simp only [smul_eq_mul, abs_of_nonneg hr2]
  ring

/-- The radial quadratic-form integrand with the actual classical derivative. -/
def radialEnergyIntegrand (r : ℝ) : ℝ :=
  ((deriv radialTrial r) ^ 2 + 4 / r ^ 2 * (radialTrial r) ^ 2 -
    radialPotential r * (radialTrial r) ^ 2) * r

/-- The same integrand after substitution, separated into Gamma and trial parts. -/
def transformedEnergyIntegrand (x : ℝ) : ℝ :=
  8 * (x ^ 3 * Real.exp (-x)) - 32 * (x ^ 2 * Real.exp (-x)) +
    64 * (x * Real.exp (-x)) -
    32 * (bernoulliRatio (x - 2) * (x ^ 2 * Real.exp (-x)))

/-- Pointwise identity on the positive radial domain. -/
theorem radial_energy_substitution_identity (r : ℝ) (hr : 0 < r) :
    radialEnergyIntegrand r = transformedEnergyIntegrand (squareRadius r) * (r / 2) := by
  have he : Real.exp (-(r ^ 2 / 8)) ^ 2 = Real.exp (-(r ^ 2 / 4)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  unfold radialEnergyIntegrand
  rw [deriv_radialTrial]
  unfold radialTrial radialPotential transformedEnergyIntegrand squareRadius
  simp only [mul_pow, he]
  field_simp
  ring

/-- The transformed kinetic and potential terms are all integrable. -/
theorem integrable_transformed_energy : IntegrableOn transformedEnergyIntegrand (Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa only [pow_one] using integrable_pow_exp_neg 1
  exact ((((integrable_pow_exp_neg 3).const_mul 8).sub
    ((integrable_pow_exp_neg 2).const_mul 32)).add (h1.const_mul 64)).sub
    (integrable_actual_trial_integrand.const_mul 32)

/-- Exact integration of the transformed expression. -/
theorem integral_transformed_energy :
    (∫ x : ℝ in Ioi 0, transformedEnergyIntegrand x) = 48 - 32 * actualTrialIntegral := by
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa only [pow_one] using integrable_pow_exp_neg 1
  have h32 : IntegrableOn
      (fun x : ℝ => 8 * (x ^ 3 * Real.exp (-x)) - 32 * (x ^ 2 * Real.exp (-x)))
      (Ioi 0) := ((integrable_pow_exp_neg 3).const_mul 8).sub
        ((integrable_pow_exp_neg 2).const_mul 32)
  have h321 : IntegrableOn
      (fun x : ℝ => 8 * (x ^ 3 * Real.exp (-x)) - 32 * (x ^ 2 * Real.exp (-x)) +
        64 * (x * Real.exp (-x))) (Ioi 0) := h32.add (h1.const_mul 64)
  unfold transformedEnergyIntegrand
  rw [integral_sub h321 (integrable_actual_trial_integrand.const_mul 32),
    integral_add h32 (h1.const_mul 64),
    integral_sub ((integrable_pow_exp_neg 3).const_mul 8)
      ((integrable_pow_exp_neg 2).const_mul 32)]
  simp only [integral_const_mul, integral_pow_exp_neg]
  have hfirst := integral_pow_exp_neg 1
  simp only [pow_one] at hfirst
  rw [hfirst]
  norm_num [Nat.factorial, actualTrialIntegral]

/-- Integrability of the literal radial trial quadratic form. -/
theorem integrable_radial_energy : IntegrableOn radialEnergyIntegrand (Ioi 0) := by
  apply (integrable_squareRadius_substitution transformedEnergyIntegrand
    integrable_transformed_energy).congr_fun _ measurableSet_Ioi
  intro r hr
  exact (radial_energy_substitution_identity r hr).symm

/-- The manuscript's identity `Q(φ)=48−32I`, with every scalar integral justified. -/
theorem integral_radial_energy :
    (∫ r : ℝ in Ioi 0, radialEnergyIntegrand r) = 48 - 32 * actualTrialIntegral := by
  calc
    (∫ r : ℝ in Ioi 0, radialEnergyIntegrand r) =
        ∫ r : ℝ in Ioi 0, transformedEnergyIntegrand (squareRadius r) * (r / 2) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          exact radial_energy_substitution_identity
    _ = ∫ x : ℝ in Ioi 0, transformedEnergyIntegrand x :=
      integral_squareRadius_substitution transformedEnergyIntegrand
    _ = 48 - 32 * actualTrialIntegral := integral_transformed_energy

/-- A genuine negative radial trial, with no spectral or integral identity assumed. -/
theorem radial_trial_strictly_negative : (∫ r : ℝ in Ioi 0, radialEnergyIntegrand r) < 0 := by
  rw [integral_radial_energy]
  exact actual_trial_expression_negative

end UnforcedLeray.GaussianQuadratic
