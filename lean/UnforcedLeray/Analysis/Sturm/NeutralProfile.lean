import UnforcedLeray.Analysis.Sturm.NeutralProfileDefs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# The explicit neutral Gaussian profile

The actual logarithmic-radius solution h*(t)=e^t(Ω(t)−e⁻²), its second-order
ODE, and its unique simple zero. The completed value of the potential is
included in the algebraic identity, so the differential equation holds also
at the critical radius.
-/

noncomputable section
namespace UnforcedLeray.Sturm
open GaussianPotential

theorem hasDerivAt_neutralRadius (t : ℝ) :
    HasDerivAt neutralRadius (2 * neutralRadius t) t := by
  have h := (((hasDerivAt_id t).const_mul 2).exp).div_const 4
  convert h using 1 <;> first | rfl | (dsimp [neutralRadius]; ring)

theorem hasDerivAt_neutralOmega (t : ℝ) :
    HasDerivAt neutralOmega (-2 * neutralRadius t * neutralOmega t) t := by
  convert (hasDerivAt_neutralRadius t).neg.exp using 1 <;>
    first | rfl | (dsimp [neutralOmega]; ring)

theorem hasDerivAt_neutralProfile (t : ℝ) :
    HasDerivAt neutralProfile
      (Real.exp t * ((1 - 2 * neutralRadius t) * neutralOmega t - Real.exp (-2))) t := by
  convert (Real.hasDerivAt_exp t).mul ((hasDerivAt_neutralOmega t).sub_const (Real.exp (-2)))
      using 1 <;> first | rfl | ring

theorem deriv_neutralProfile (t : ℝ) :
    deriv neutralProfile t =
      Real.exp t * ((1 - 2 * neutralRadius t) * neutralOmega t - Real.exp (-2)) :=
  (hasDerivAt_neutralProfile t).deriv

theorem hasDerivAt_deriv_neutralProfile (t : ℝ) :
    HasDerivAt (deriv neutralProfile)
      (Real.exp t * ((1 - 8 * neutralRadius t + 4 * neutralRadius t ^ 2) *
        neutralOmega t - Real.exp (-2))) t := by
  have hx := hasDerivAt_neutralRadius t
  have ho := hasDerivAt_neutralOmega t
  have hpoly : HasDerivAt (fun s => 1 - 2 * neutralRadius s)
      (-4 * neutralRadius t) t := by
    convert (hx.const_mul 2).const_sub 1 using 1 <;> first | rfl | ring
  have h := (Real.hasDerivAt_exp t).mul
    ((hpoly.mul ho).sub_const (Real.exp (-2)))
  have he : deriv neutralProfile = fun s =>
      Real.exp s * ((1 - 2 * neutralRadius s) * neutralOmega s - Real.exp (-2)) :=
    funext deriv_neutralProfile
  rw [he]
  convert h using 1 <;> first | rfl | (dsimp; ring)

theorem deriv_deriv_neutralProfile (t : ℝ) :
    deriv (deriv neutralProfile) t =
      Real.exp t * ((1 - 8 * neutralRadius t + 4 * neutralRadius t ^ 2) *
        neutralOmega t - Real.exp (-2)) :=
  (hasDerivAt_deriv_neutralProfile t).deriv

/-- The potential cancellation, including the actual removable value. -/
theorem W_mul_neutral_difference (y : ℝ) :
    W y * (Real.exp (-(y + 2)) - Real.exp (-2)) =
      -4 * (y + 2) * y * Real.exp (-(y + 2)) := by
  by_cases hy : y = 0
  · subst y
    simp
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
  rw [W, ite_eq_right hy, hdiff]
  field_simp

/-- The exact neutral ODE on the whole log-radius line. -/
theorem neutralProfile_ode (t : ℝ) :
    deriv (deriv neutralProfile) t = (1 - Wlog t) * neutralProfile t := by
  have hw := W_mul_neutral_difference (neutralRadius t - 2)
  have hcancel : Wlog t * (neutralOmega t - Real.exp (-2)) =
      -4 * neutralRadius t * (neutralRadius t - 2) * neutralOmega t := by
    simpa only [sub_add_cancel, neutralOmega, Wlog, neutralRadius] using hw
  rw [deriv_deriv_neutralProfile, neutralProfile]
  linear_combination Real.exp t * hcancel

@[simp] theorem neutralRadius_at_critical : neutralRadius neutralCriticalTime = 2 := by
  unfold neutralRadius neutralCriticalTime
  rw [show 2 * (Real.log 8 / 2) = Real.log 8 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  norm_num

@[simp] theorem neutralOmega_at_critical : neutralOmega neutralCriticalTime = Real.exp (-2) := by
  simp [neutralOmega]

/-- The explicit neutral solution has exactly one zero. -/
theorem neutralProfile_eq_zero_iff (t : ℝ) :
    neutralProfile t = 0 ↔ t = neutralCriticalTime := by
  constructor
  · intro ht
    have ho : neutralOmega t = Real.exp (-2) := by
      have hzero := (mul_eq_zero.mp ht).resolve_left (Real.exp_ne_zero t)
      exact sub_eq_zero.mp hzero
    have hx : neutralRadius t = 2 := by
      have := Real.exp_injective ho
      change -neutralRadius t = -2 at this
      linarith
    have he : Real.exp (2 * t) = 8 := by
      unfold neutralRadius at hx
      linarith
    have hl := congrArg Real.log he
    rw [Real.log_exp] at hl
    unfold neutralCriticalTime
    linarith
  · rintro rfl
    simp [neutralProfile]

/-- Nonvanishing away from the unique critical point. -/
theorem neutralProfile_ne_zero {t : ℝ} (ht : t ≠ neutralCriticalTime) :
    neutralProfile t ≠ 0 := by
  intro hz
  exact ht ((neutralProfile_eq_zero_iff t).mp hz)

/-- The zero is simple, with its actual strictly negative derivative. -/
theorem deriv_neutralProfile_at_critical :
    deriv neutralProfile neutralCriticalTime =
      -4 * Real.exp neutralCriticalTime * Real.exp (-2) := by
  rw [deriv_neutralProfile, neutralRadius_at_critical, neutralOmega_at_critical]
  ring

theorem deriv_neutralProfile_at_critical_neg : deriv neutralProfile neutralCriticalTime < 0 := by
  rw [deriv_neutralProfile_at_critical]
  have h1 := Real.exp_pos neutralCriticalTime
  have h2 := Real.exp_pos (-2)
  nlinarith

theorem neutralProfile_deriv_critical_ne_zero :
    deriv neutralProfile neutralCriticalTime ≠ 0 :=
  ne_of_lt deriv_neutralProfile_at_critical_neg

end UnforcedLeray.Sturm
