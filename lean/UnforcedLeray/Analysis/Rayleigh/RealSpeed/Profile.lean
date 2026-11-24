import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Defs

/-!
# The actual comparison profile at every real speed

The explicit h_c(t)=exp(t)(Ω(t)−c) solves its comparison equation wherever
Ω(t)≠c. The numerator identity holds globally, even at a critical point.
Strict monotonicity of the actual Gaussian angular speed makes a critical
point unique. No spectral speed restriction is assumed.
-/

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm GaussianPotential

/-- The actual Gaussian angular speed is strictly decreasing on the whole line. -/
theorem neutralOmega_strictAnti : StrictAnti neutralOmega := by
  apply strictAnti_of_hasDerivAt_neg hasDerivAt_neutralOmega
  intro t
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (neutralRadius_pos t)) (neutralOmega_pos t)

theorem neutralOmega_injective : Function.Injective neutralOmega := neutralOmega_strictAnti.injective

theorem speedProfile_smooth (c : ℝ) : ContDiff ℝ ∞ (speedProfile c) := by
  unfold speedProfile neutralOmega neutralRadius
  fun_prop

theorem hasDerivAt_speedProfile (c t : ℝ) :
    HasDerivAt (speedProfile c)
      (Real.exp t * ((1 - 2 * neutralRadius t) * neutralOmega t - c)) t := by
  convert (Real.hasDerivAt_exp t).mul ((hasDerivAt_neutralOmega t).sub_const c)
      using 1 <;> first | rfl | ring

theorem deriv_speedProfile (c t : ℝ) :
    deriv (speedProfile c) t =
      Real.exp t * ((1 - 2 * neutralRadius t) * neutralOmega t - c) :=
  (hasDerivAt_speedProfile c t).deriv

theorem hasDerivAt_deriv_speedProfile (c t : ℝ) :
    HasDerivAt (deriv (speedProfile c))
      (Real.exp t * ((1 - 8 * neutralRadius t + 4 * neutralRadius t ^ 2) *
        neutralOmega t - c)) t := by
  have hx := hasDerivAt_neutralRadius t
  have ho := hasDerivAt_neutralOmega t
  have hpoly : HasDerivAt (fun s => 1 - 2 * neutralRadius s)
      (-4 * neutralRadius t) t := by
    convert (hx.const_mul 2).const_sub 1 using 1 <;> first | rfl | ring
  have h := (Real.hasDerivAt_exp t).mul ((hpoly.mul ho).sub_const c)
  have he : deriv (speedProfile c) = fun s =>
      Real.exp s * ((1 - 2 * neutralRadius s) * neutralOmega s - c) :=
    funext (deriv_speedProfile c)
  rw [he]
  convert h using 1 <;> first | rfl | (dsimp; ring)

theorem deriv_deriv_speedProfile (c t : ℝ) :
    deriv (deriv (speedProfile c)) t =
      Real.exp t * ((1 - 8 * neutralRadius t + 4 * neutralRadius t ^ 2) *
        neutralOmega t - c) :=
  (hasDerivAt_deriv_speedProfile c t).deriv

/-- The comparison equation in numerator form, with no denominator or exception. -/
theorem speedProfile_second_global (c t : ℝ) :
    deriv (deriv (speedProfile c)) t =
      Real.exp t * (neutralOmega t - c + gaussianRayleighCoefficient t) := by
  rw [deriv_deriv_speedProfile, gaussianRayleighCoefficient_eq]
  ring

/-- The exact comparison ODE at every nonsingular real-speed point. -/
theorem speedProfile_ode {c t : ℝ} (hc : neutralOmega t ≠ c) :
    deriv (deriv (speedProfile c)) t =
      (1 + gaussianRayleighCoefficient t / (neutralOmega t - c)) * speedProfile c t := by
  rw [speedProfile_second_global, speedProfile]
  have hd : neutralOmega t - c ≠ 0 := sub_ne_zero.mpr hc
  field_simp

theorem speedProfile_ode_potential {c t : ℝ} (hc : neutralOmega t ≠ c) :
    deriv (deriv (speedProfile c)) t = speedPotential c t * speedProfile c t := by
  simpa only [speedPotential] using speedProfile_ode hc

/-- The zero set is exactly the actual critical-level set of Ω. -/
theorem speedProfile_eq_zero_iff (c t : ℝ) :
    speedProfile c t = 0 ↔ neutralOmega t = c := by
  simp only [speedProfile, mul_eq_zero, Real.exp_ne_zero, false_or, sub_eq_zero]

theorem speedProfile_ne_zero_iff (c t : ℝ) :
    speedProfile c t ≠ 0 ↔ neutralOmega t ≠ c :=
  not_congr (speedProfile_eq_zero_iff c t)

/-- A real speed has at most one critical point. -/
theorem speedProfile_unique_zero {c s t : ℝ}
    (hs : speedProfile c s = 0) (ht : speedProfile c t = 0) : s = t := by
  apply neutralOmega_injective
  exact ((speedProfile_eq_zero_iff c s).mp hs).trans ((speedProfile_eq_zero_iff c t).mp ht).symm

theorem speedProfile_ne_zero_off {c a t : ℝ} (ha : neutralOmega a = c) (ht : t ≠ a) :
    speedProfile c t ≠ 0 := by
  rw [speedProfile_ne_zero_iff]
  intro he
  exact ht (neutralOmega_injective (he.trans ha.symm))

theorem speedProfile_ne_zero_of_not_exists {c : ℝ} (hc : ¬ ∃ a, neutralOmega a = c)
    (t : ℝ) : speedProfile c t ≠ 0 := by
  rw [speedProfile_ne_zero_iff]
  exact fun ht => hc ⟨t, ht⟩

/-- Endpoint and exterior speeds have no singular point on the finite real line. -/
theorem neutralOmega_ne_of_outside {c : ℝ} (hc : c ≤ 0 ∨ 1 ≤ c) (t : ℝ) :
    neutralOmega t ≠ c := by
  rcases hc with hc | hc
  · exact ne_of_gt (lt_of_le_of_lt hc (neutralOmega_pos t))
  · exact ne_of_lt ((neutralOmega_lt_one t).trans_le hc)

theorem speedProfile_ne_zero_of_outside {c : ℝ} (hc : c ≤ 0 ∨ 1 ≤ c) (t : ℝ) :
    speedProfile c t ≠ 0 :=
  (speedProfile_ne_zero_iff c t).mpr (neutralOmega_ne_of_outside hc t)

end UnforcedLeray.Rayleigh.RealSpeed
