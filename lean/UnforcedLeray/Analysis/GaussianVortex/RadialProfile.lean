import UnforcedLeray.Analysis.Rayleigh.GaussianMode
import UnforcedLeray.GaussianTrial
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# The manuscript's actual radial Gaussian vortex profiles

These functions have unit vortex amplitude. All derivatives are classical
one-dimensional derivatives of the explicit profiles, including at radius
zero. The logarithmic-coordinate identities connect them to the existing
Rayleigh coefficients without an assumed change-of-variables identity.
-/

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.GaussianVortex
open GaussianTrial

/-- Angular velocity at unit vortex amplitude. -/
def radialOmega (r : ℝ) : ℝ := Real.exp (-(r ^ 2 / 4))

/-- Actual scalar vorticity of the Gaussian vortex. -/
def radialVorticity (r : ℝ) : ℝ := (2 - r ^ 2 / 2) * radialOmega r

/-- Smooth completion of the vorticity derivative divided by radius. -/
def radialK (r : ℝ) : ℝ := (r ^ 2 / 4 - 2) * radialOmega r

/-- The streamfunction in the convention u=∇⊥ψ and curl u=Δψ. -/
def radialStreamfunction (r : ℝ) : ℝ := -2 * radialOmega r

theorem radialOmega_pos (r : ℝ) : 0 < radialOmega r := Real.exp_pos _

theorem radialOmega_smooth : ContDiff ℝ ∞ radialOmega := by
  unfold radialOmega
  fun_prop

theorem radialVorticity_smooth : ContDiff ℝ ∞ radialVorticity := by
  unfold radialVorticity radialOmega
  fun_prop

theorem radialK_smooth : ContDiff ℝ ∞ radialK := by
  unfold radialK radialOmega
  fun_prop

theorem radialStreamfunction_smooth : ContDiff ℝ ∞ radialStreamfunction := by
  unfold radialStreamfunction radialOmega
  fun_prop

/-- The angular velocity derivative is computed from its actual exponential. -/
theorem hasDerivAt_radialOmega (r : ℝ) :
    HasDerivAt radialOmega (-r / 2 * radialOmega r) r := by
  convert (((hasDerivAt_id r).pow 2).div_const 4).neg.exp using 1
  all_goals first | rfl | (dsimp [radialOmega]; ring)

theorem deriv_radialOmega (r : ℝ) :
    deriv radialOmega r = -r / 2 * radialOmega r :=
  (hasDerivAt_radialOmega r).deriv

theorem hasDerivAt_radialStreamfunction (r : ℝ) :
    HasDerivAt radialStreamfunction (r * radialOmega r) r := by
  convert (hasDerivAt_radialOmega r).const_mul (-2) using 1
  all_goals first | rfl | ring

theorem deriv_radialStreamfunction (r : ℝ) :
    deriv radialStreamfunction r = r * radialOmega r :=
  (hasDerivAt_radialStreamfunction r).deriv

/-- This identity is valid at zero as well as at positive radii. -/
theorem hasDerivAt_radialVorticity (r : ℝ) :
    HasDerivAt radialVorticity (r * radialK r) r := by
  convert ((((hasDerivAt_id r).pow 2).div_const 2).const_sub 2).mul
    (hasDerivAt_radialOmega r) using 1
  all_goals first | rfl | (dsimp [radialK]; ring)

theorem deriv_radialVorticity (r : ℝ) :
    deriv radialVorticity r = r * radialK r :=
  (hasDerivAt_radialVorticity r).deriv

theorem radialK_eq_deriv_div {r : ℝ} (hr : r ≠ 0) :
    radialK r = deriv radialVorticity r / r := by
  rw [deriv_radialVorticity]
  field_simp

/-- The actual second angular-velocity derivative. -/
theorem hasDerivAt_deriv_radialOmega (r : ℝ) :
    HasDerivAt (deriv radialOmega) ((r ^ 2 / 4 - 1 / 2) * radialOmega r) r := by
  rw [show deriv radialOmega = fun s => -s / 2 * radialOmega s from funext deriv_radialOmega]
  convert (((hasDerivAt_id r).neg.div_const 2).mul (hasDerivAt_radialOmega r)) using 1
  all_goals first | rfl | (dsimp; ring)

theorem deriv_deriv_radialOmega (r : ℝ) :
    deriv (deriv radialOmega) r = (r ^ 2 / 4 - 1 / 2) * radialOmega r :=
  (hasDerivAt_deriv_radialOmega r).deriv

/-- The numerator in Lin's rotating-flow criterion is exactly E₀'. -/
theorem radial_lin_numerator (r : ℝ) :
    r * deriv (deriv radialOmega) r + 3 * deriv radialOmega r = r * radialK r := by
  rw [deriv_deriv_radialOmega, deriv_radialOmega, radialK]
  ring

theorem deriv_radialOmega_neg {r : ℝ} (hr : 0 < r) : deriv radialOmega r < 0 := by
  rw [deriv_radialOmega]
  exact mul_neg_of_neg_of_pos (by linarith) (radialOmega_pos r)

/-- Strict monotonicity is proved on the full nonnegative radius axis. -/
theorem strictAntiOn_radialOmega : StrictAntiOn radialOmega (Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  apply Real.exp_lt_exp.mpr
  have hp : 0 < (b - a) * (b + a) := mul_pos (sub_pos.mpr hab) (by linarith [ha])
  nlinarith

theorem radialOmega_critical_iff (r : ℝ) :
    radialOmega r = Real.exp (-2) ↔ r ^ 2 = 8 := by
  constructor
  · intro h
    have he := Real.exp_injective h
    change -(r ^ 2 / 4) = -2 at he
    linarith
  · intro h
    unfold radialOmega
    congr 1
    linarith

theorem radialK_zero_iff (r : ℝ) : radialK r = 0 ↔ r ^ 2 = 8 := by
  rw [radialK, mul_eq_zero]
  have hn : radialOmega r ≠ 0 := (radialOmega_pos r).ne'
  simp only [hn, or_false]
  constructor <;> intro h <;> linarith

/-- The nonnegative critical radius is exactly √8. -/
theorem radialOmega_critical_iff_sqrt {r : ℝ} (hr : 0 ≤ r) :
    radialOmega r = Real.exp (-2) ↔ r = Real.sqrt 8 := by
  rw [radialOmega_critical_iff]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  have hp := Real.sqrt_nonneg (8 : ℝ)
  constructor
  · intro h
    nlinarith
  · rintro rfl
    exact hs

theorem radialOmega_at_sqrt_eight : radialOmega (Real.sqrt 8) = Real.exp (-2) :=
  (radialOmega_critical_iff_sqrt (Real.sqrt_nonneg _)).mpr rfl

theorem radialOmega_critical_nondegenerate : deriv radialOmega (Real.sqrt 8) ≠ 0 := by
  exact (deriv_radialOmega_neg (Real.sqrt_pos.mpr (by norm_num))).ne

/-- The actual exponential substitution r=eᵗ. -/
theorem exp_sq_eq_exp_twice (t : ℝ) : (Real.exp t) ^ 2 = Real.exp (2 * t) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem radialOmega_exp (t : ℝ) : radialOmega (Real.exp t) = Sturm.neutralOmega t := by
  simp only [radialOmega, Sturm.neutralOmega, Sturm.neutralRadius, exp_sq_eq_exp_twice]

theorem radialVorticity_exp (t : ℝ) :
    radialVorticity (Real.exp t) = Rayleigh.gaussianVorticity t := by
  rw [radialVorticity, radialOmega_exp, Rayleigh.gaussianVorticity, Sturm.neutralRadius,
    exp_sq_eq_exp_twice]
  ring

theorem radial_vorticity_log_derivative (t : ℝ) :
    Real.exp t * deriv radialVorticity (Real.exp t) =
      Rayleigh.gaussianRayleighCoefficient t := by
  rw [deriv_radialVorticity, radialK, radialOmega_exp,
    Rayleigh.gaussianRayleighCoefficient_eq, Sturm.neutralRadius]
  rw [← exp_sq_eq_exp_twice]
  ring

/-- The completed ratio obeys its cancellation identity also at zero. -/
theorem bernoulliRatio_mul_exp_difference (y : ℝ) :
    bernoulliRatio y * (Real.exp (-(y + 2)) - Real.exp (-2)) =
      -y * Real.exp (-(y + 2)) := by
  by_cases hy : y = 0
  · subst y
    simp [bernoulliRatio]
  have hd : Real.exp y - 1 ≠ 0 := by
    intro he
    apply hy
    apply Real.exp_injective
    simpa only [Real.exp_zero] using sub_eq_zero.mp he
  have hexp : Real.exp y * Real.exp (-(y + 2)) = Real.exp (-2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiff : Real.exp (-(y + 2)) - Real.exp (-2) =
      -(Real.exp y - 1) * Real.exp (-(y + 2)) := by
    rw [← hexp]
    ring
  rw [bernoulliRatio, ite_eq_right hy, hdiff]
  field_simp

theorem radialOmega_ne_critical {r : ℝ} (hr : r ^ 2 ≠ 8) :
    radialOmega r ≠ Real.exp (-2) := by
  intro h
  apply hr
  have he := Real.exp_injective h
  change -(r ^ 2 / 4) = -2 at he
  linarith

/-- The actual radial potential quotient, away from the removable critical value. -/
theorem radial_potential_quotient {r : ℝ} (hr : r ^ 2 ≠ 8) :
    -radialK r / (radialOmega r - Real.exp (-2)) =
      bernoulliRatio (r ^ 2 / 4 - 2) := by
  have h := bernoulliRatio_mul_exp_difference (r ^ 2 / 4 - 2)
  have hd : radialOmega r - Real.exp (-2) ≠ 0 :=
    sub_ne_zero.mpr (radialOmega_ne_critical hr)
  apply (div_eq_iff hd).mpr
  simpa only [sub_add_cancel, radialOmega, radialK, neg_mul] using h.symm

theorem bernoulliRatio_pos (y : ℝ) : 0 < bernoulliRatio y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [bernoulliRatio, ite_eq_right hy.ne]
    exact div_pos_of_neg_of_neg hy (sub_neg.mpr (Real.exp_lt_one_iff.mpr hy))
  · subst y
    simp [bernoulliRatio]
  · rw [bernoulliRatio, ite_eq_right hy.ne']
    exact div_pos hy (sub_pos.mpr (Real.one_lt_exp_iff.mpr hy))

theorem radial_lin_completed_pos {r : ℝ} (hr : 0 < r) :
    0 < r * bernoulliRatio (r ^ 2 / 4 - 2) :=
  mul_pos hr (bernoulliRatio_pos _)

theorem radial_lin_completed_at_critical {r : ℝ} (hr : r ^ 2 = 8) :
    r * bernoulliRatio (r ^ 2 / 4 - 2) = r := by
  rw [hr]
  norm_num [bernoulliRatio]


/-- Lin's actual derivative coefficient equals its completed positive profile
away from the removable critical radius. -/
theorem radial_lin_coefficient {r : ℝ} (hr : r ^ 2 ≠ 8) :
    -(r * deriv (deriv radialOmega) r + 3 * deriv radialOmega r) /
      (radialOmega r - Real.exp (-2)) =
      r * bernoulliRatio (r ^ 2 / 4 - 2) := by
  rw [radial_lin_numerator]
  calc
    _ = r * (-radialK r / (radialOmega r - Real.exp (-2))) := by ring
    _ = _ := by rw [radial_potential_quotient hr]

/-- Polar-coordinate curl of the actual angular velocity profile. -/
theorem radialVorticity_eq_radial_curl (r : ℝ) :
    radialVorticity r = 2 * radialOmega r + r * deriv radialOmega r := by
  rw [radialVorticity, deriv_radialOmega]
  ring

end UnforcedLeray.GaussianVortex
