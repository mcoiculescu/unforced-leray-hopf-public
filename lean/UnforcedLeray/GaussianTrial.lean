import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Rational part of the Gaussian negative trial

These lemmas formalize the scalar integral lower bound in `paper/main.tex`,
equations `eq:st18-t00025` through `eq:st18-t00027`. The proof includes the
pointwise hyperbolic bound, the explicit removable value at zero, integrability,
the actual Gamma moments, and the rational square completion. The resulting
`actual_trial_integral_lower_bound` has no hypotheses.

The identification of `48 - 32 * actualTrialIntegral` with the manuscript's
Sturm quadratic form, spectral instability, and the Navier–Stokes construction
are separate obligations and are not asserted here. The final generic integral
lemmas expose their moment hypotheses explicitly and are not used to bypass the
actual moment proofs.
-/

noncomputable section

namespace UnforcedLeray.GaussianTrial

open MeasureTheory

/-- The polynomial used in the manuscript's square completion. -/
def trialP (y : ℝ) : ℝ := y * (16 - y) / 930

/-- The polynomial numerator after substituting `trialP`. -/
def trialPolynomial (y : ℝ) : ℝ :=
  (14400 * y ^ 2 + 60 * y ^ 3 - 316 * y ^ 4 + 32 * y ^ 5 - y ^ 6) / 864900

/-- Exact nonnegative remainder in the rational square-completion bound. -/
theorem square_completion_identity (y p : ℝ) :
    y ^ 2 / (60 + y ^ 2) - (2 * y * p - (60 + y ^ 2) * p ^ 2) =
      (y - (60 + y ^ 2) * p) ^ 2 / (60 + y ^ 2) := by
  have hd : (60 : ℝ) + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- Equation `eq:st18-t00026`, valid for every real choice of `p`. -/
theorem square_completion_lower_bound (y p : ℝ) :
    2 * y * p - (60 + y ^ 2) * p ^ 2 ≤ y ^ 2 / (60 + y ^ 2) := by
  have h := div_nonneg (sq_nonneg (y - (60 + y ^ 2) * p))
    (show (0 : ℝ) ≤ 60 + y ^ 2 by positivity)
  rw [← square_completion_identity y p] at h
  linarith

/-- Exact expansion; every coefficient is checked in the real field. -/
theorem trial_polynomial_expansion (y : ℝ) :
    2 * y * trialP y - (60 + y ^ 2) * (trialP y) ^ 2 = trialPolynomial y := by
  unfold trialP trialPolynomial
  ring

/-- The manuscript's explicit polynomial is a pointwise lower bound. -/
theorem trial_polynomial_le_fraction (y : ℝ) :
    trialPolynomial y ≤ y ^ 2 / (60 + y ^ 2) := by
  rw [← trial_polynomial_expansion]
  exact square_completion_lower_bound y (trialP y)

/-- The exact moment arithmetic, isolated from any analytic moment claims. -/
theorem moment_arithmetic :
    ((14400 : ℝ) * 8 + 60 * 32 - 316 * 176 + 32 * 1136 - 8576) / 864900 =
      16 / 155 := by
  norm_num

/-- Combining the two elementary moment terms with the rational improvement. -/
theorem scalar_trial_lower_bound (I J : ℝ) (hI : I ≥ 2 - 1 + 5 * J)
    (hJ : J ≥ 16 / 155) : I ≥ 47 / 31 := by
  linarith

/-- The strictly negative trial value follows from the claimed lower bound for `I`. -/
theorem negative_trial_bound (I : ℝ) (hI : I ≥ 47 / 31) :
    48 - 32 * I ≤ -(16 / 31 : ℝ) := by
  linarith

/-- The rational upper bound is strictly negative. -/
theorem negative_trial_strict (I : ℝ) (hI : I ≥ 47 / 31) :
    48 - 32 * I < 0 := by
  have := negative_trial_bound I hI
  linarith

section HyperbolicBound

open Set

private theorem nonneg_of_nonneg_deriv (f f' : ℝ → ℝ) (h0 : f 0 = 0)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) (z : ℝ) (hz : 0 ≤ z) : 0 ≤ f z := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hm : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hc.continuousOn
      (fun x _ => (hf x).hasDerivWithinAt)
      (fun x hx => hpos x (interior_subset hx))
  simpa only [h0] using hm (show (0 : ℝ) ∈ Ici 0 by simp) hz hz

/-- First step in an elementary derivative proof of the hyperbolic bound. -/
theorem mul_cosh_sub_sinh_nonneg (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ z * Real.cosh z - Real.sinh z := by
  apply nonneg_of_nonneg_deriv (fun z => z * Real.cosh z - Real.sinh z)
    (fun z => z * Real.sinh z) (by simp) _ _ z hz
  · intro x
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1 <;> first | rfl | (dsimp; ring)
  · intro x hx
    exact mul_nonneg hx (Real.sinh_nonneg_iff.mpr hx)

/-- Second step in the derivative proof. -/
theorem quadratic_sinh_sub_cosh_nonneg (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (z ^ 2 + 3) * Real.sinh z - 3 * z * Real.cosh z := by
  apply nonneg_of_nonneg_deriv
    (fun z => (z ^ 2 + 3) * Real.sinh z - 3 * z * Real.cosh z)
    (fun z => z * (z * Real.cosh z - Real.sinh z)) (by simp) _ _ z hz
  · intro x
    convert ((((hasDerivAt_id x).pow 2).add_const 3).mul
      (Real.hasDerivAt_sinh x)).sub
      (((hasDerivAt_id x).const_mul 3).mul (Real.hasDerivAt_cosh x)) using 1 <;> first | rfl | (dsimp; ring)
  · intro x hx
    exact mul_nonneg hx (mul_cosh_sub_sinh_nonneg x hx)

/-- The manuscript's hyperbolic numerator is nonnegative, proved by differentiation. -/
theorem cubic_cosh_sub_sinh_nonneg (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (z ^ 3 + 15 * z) * Real.cosh z - (6 * z ^ 2 + 15) * Real.sinh z := by
  apply nonneg_of_nonneg_deriv
    (fun z => (z ^ 3 + 15 * z) * Real.cosh z - (6 * z ^ 2 + 15) * Real.sinh z)
    (fun z => z * ((z ^ 2 + 3) * Real.sinh z - 3 * z * Real.cosh z))
    (by simp) _ _ z hz
  · intro x
    convert ((((hasDerivAt_id x).pow 3).add ((hasDerivAt_id x).const_mul 15)).mul
      (Real.hasDerivAt_cosh x)).sub
      (((((hasDerivAt_id x).pow 2).const_mul 6).add_const 15).mul
        (Real.hasDerivAt_sinh x)) using 1 <;> first | rfl | (dsimp; ring)
  · intro x hx
    exact mul_nonneg hx (quadratic_sinh_sub_cosh_nonneg x hx)

/-- The useful rational lower bound for `z coth z` at positive `z`. -/
theorem coth_rational_lower_bound_pos (z : ℝ) (hz : 0 < z) :
    1 + 5 * z ^ 2 / (15 + z ^ 2) ≤ z * Real.cosh z / Real.sinh z := by
  have hs : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hd : (0 : ℝ) < 15 + z ^ 2 := by positivity
  apply (le_div_iff₀ hs).2
  have h := cubic_cosh_sub_sinh_nonneg z hz.le
  calc
    (1 + 5 * z ^ 2 / (15 + z ^ 2)) * Real.sinh z =
        ((15 + 6 * z ^ 2) * Real.sinh z) / (15 + z ^ 2) := by
          field_simp
          ring
    _ ≤ z * Real.cosh z := (div_le_iff₀ hd).2 (by nlinarith)

/-- Evenness extends the bound to every nonzero real input. -/
theorem coth_rational_lower_bound (z : ℝ) (hz : z ≠ 0) :
    1 + 5 * z ^ 2 / (15 + z ^ 2) ≤ z * Real.cosh z / Real.sinh z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simpa [Real.cosh_neg, Real.sinh_neg] using
      coth_rational_lower_bound_pos (-z) (neg_pos.mpr hneg)
  · exact coth_rational_lower_bound_pos z hpos

/-- The removable value at zero is part of the mathematical definition of `g`. -/
def bernoulliRatio (y : ℝ) : ℝ := if y = 0 then 1 else y / (Real.exp y - 1)

private theorem exp_double_sub_one (z : ℝ) :
    Real.exp (2 * z) - 1 = 2 * Real.exp z * Real.sinh z := by
  rw [two_mul, Real.exp_add, Real.sinh_eq, Real.exp_neg]
  field_simp

/-- Exact exponential/hyperbolic identity, away from the removable point. -/
theorem exp_ratio_eq_coth_sub (z : ℝ) (hz : z ≠ 0) :
    (2 * z) / (Real.exp (2 * z) - 1) = z * Real.cosh z / Real.sinh z - z := by
  have hs : Real.sinh z ≠ 0 := mt Real.sinh_eq_zero.mp hz
  calc
    (2 * z) / (Real.exp (2 * z) - 1) = z / (Real.exp z * Real.sinh z) := by
      rw [exp_double_sub_one]
      field_simp
    _ = z * (Real.cosh z - Real.sinh z) / Real.sinh z := by
      rw [Real.cosh_sub_sinh, Real.exp_neg]
      ring
    _ = z * Real.cosh z / Real.sinh z - z := by
      field_simp

/-- Equation `eq:st18-t00025`, including the correctly filled removable value. -/
theorem bernoulli_rational_lower_bound (y : ℝ) :
    1 - y / 2 + 5 * y ^ 2 / (60 + y ^ 2) ≤ bernoulliRatio y := by
  by_cases hy : y = 0
  · simp [bernoulliRatio, hy]
  have hz : y / 2 ≠ 0 := div_ne_zero hy (by norm_num)
  have hc := coth_rational_lower_bound (y / 2) hz
  have hi := exp_ratio_eq_coth_sub (y / 2) hz
  have hy2 : 2 * (y / 2) = y := by ring
  rw [hy2] at hi
  have hr : 5 * (y / 2) ^ 2 / (15 + (y / 2) ^ 2) =
      5 * y ^ 2 / (60 + y ^ 2) := by
    field_simp
    ring
  rw [hr] at hc
  rw [bernoulliRatio, ite_eq_right hy, hi]
  linarith

/-- On the positive axis the exponential-ratio factor lies in `[0,1]`. -/
theorem bernoulli_bounds_pos (y : ℝ) (hy : 0 < y) :
    0 ≤ bernoulliRatio y ∧ bernoulliRatio y ≤ 1 := by
  have hd : 0 < Real.exp y - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hy)
  rw [bernoulliRatio, ite_eq_right (ne_of_gt hy)]
  constructor
  · positivity
  · apply (div_le_one hd).2
    have he := Real.add_one_le_exp y
    linarith

/-- Reflection formula, used to control the factor for negative inputs. -/
theorem bernoulli_neg (y : ℝ) (hy : y ≠ 0) :
    bernoulliRatio (-y) = bernoulliRatio y + y := by
  have hn : -y ≠ 0 := neg_ne_zero.mpr hy
  have hd : Real.exp y - 1 ≠ 0 := by
    intro h
    have he : Real.exp y = Real.exp 0 := by simp only [Real.exp_zero]; linarith
    exact hy (Real.exp_injective he)
  have hd' : (1 : ℝ) - Real.exp y ≠ 0 := by
    intro h
    apply hd
    linarith
  rw [bernoulliRatio, ite_eq_right hn, bernoulliRatio, ite_eq_right hy, Real.exp_neg]
  field_simp [hd, hd']
  ring

/-- A global linear majorant, with the removable value included. -/
theorem bernoulli_bounds (y : ℝ) :
    0 ≤ bernoulliRatio y ∧ bernoulliRatio y ≤ 1 + |y| := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hp := bernoulli_bounds_pos (-y) (neg_pos.mpr hy)
    have hr := bernoulli_neg (-y) (ne_of_gt (neg_pos.mpr hy))
    simp only [neg_neg] at hr
    rw [hr, abs_of_neg hy]
    constructor <;> linarith [hp.1, hp.2]
  · subst y
    simp [bernoulliRatio]
  · have hp := bernoulli_bounds_pos y hy
    rw [abs_of_pos hy]
    exact ⟨hp.1, by linarith [hp.2]⟩

/-- Measurability does not require separately proving continuity at the filled point. -/
theorem measurable_bernoulliRatio : Measurable bernoulliRatio := by
  unfold bernoulliRatio
  exact Measurable.ite (by measurability) measurable_const
    (measurable_id.div (Real.continuous_exp.measurable.sub measurable_const))

end HyperbolicBound

section ActualMoments

open Set

/-- The actual factorial integral used for the manuscript's Gaussian trial. -/
theorem integral_pow_exp_neg (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ n * Real.exp (-x)) = (n.factorial : ℝ) := by
  have h := (Real.Gamma_eq_integral (show (0 : ℝ) < n + 1 by positivity)).symm
  simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm,
    Real.Gamma_nat_eq_factorial] using h

/-- Integrability, separately checked so that integral linearity is legitimate. -/
theorem integrable_pow_exp_neg (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (show (0 : ℝ) < n + 1 by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using h

/-- Finite binomial expansion before integrating the shifted moments. -/
theorem shifted_moment_expansion (n : ℕ) (x : ℝ) :
    (x - 2) ^ n * (x ^ 2 * Real.exp (-x)) =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * (-2) ^ (n - j)) * (x ^ (j + 2) * Real.exp (-x)) := by
  rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Exact finite formula for every actual shifted moment. -/
theorem integral_shifted_moment (n : ℕ) :
    (∫ x : ℝ in Ioi 0, (x - 2) ^ n * (x ^ 2 * Real.exp (-x))) =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * (-2) ^ (n - j)) * ((j + 2).factorial : ℝ) := by
  simp_rw [shifted_moment_expansion]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_pow_exp_neg]
  · intro j hj
    exact (integrable_pow_exp_neg (j + 2)).const_mul _

/-- Every shifted moment occurring in the trial polynomial is integrable. -/
theorem integrable_shifted_moment (n : ℕ) :
    IntegrableOn (fun x : ℝ => (x - 2) ^ n * (x ^ 2 * Real.exp (-x))) (Ioi 0) := by
  simp_rw [shifted_moment_expansion]
  exact integrable_finsetSum _ (fun j hj => (integrable_pow_exp_neg (j + 2)).const_mul _)

/-- All seven moment values displayed in the manuscript, for the actual density. -/
theorem actual_shifted_moments :
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 0 * (x ^ 2 * Real.exp (-x))) = 2 ∧
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 1 * (x ^ 2 * Real.exp (-x))) = 2 ∧
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 2 * (x ^ 2 * Real.exp (-x))) = 8 ∧
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 3 * (x ^ 2 * Real.exp (-x))) = 32 ∧
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 4 * (x ^ 2 * Real.exp (-x))) = 176 ∧
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 5 * (x ^ 2 * Real.exp (-x))) = 1136 ∧
    (∫ x : ℝ in Ioi 0, (x - 2) ^ 6 * (x ^ 2 * Real.exp (-x))) = 8576 := by
  simp_rw [integral_shifted_moment]
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]

/-- The pointwise weighted polynomial expansion used for its exact integral. -/
theorem weighted_trial_expansion (x : ℝ) :
    trialPolynomial (x - 2) * (x ^ 2 * Real.exp (-x)) =
      (14400 * ((x - 2) ^ 2 * (x ^ 2 * Real.exp (-x))) +
        60 * ((x - 2) ^ 3 * (x ^ 2 * Real.exp (-x))) -
        316 * ((x - 2) ^ 4 * (x ^ 2 * Real.exp (-x))) +
        32 * ((x - 2) ^ 5 * (x ^ 2 * Real.exp (-x))) -
        (x - 2) ^ 6 * (x ^ 2 * Real.exp (-x))) / 864900 := by
  unfold trialPolynomial
  ring

/-- The actual polynomial lower bound is integrable against `x² exp(-x) dx`. -/
theorem integrable_actual_trial_polynomial :
    IntegrableOn (fun x : ℝ => trialPolynomial (x - 2) * (x ^ 2 * Real.exp (-x)))
      (Ioi 0) := by
  simp_rw [weighted_trial_expansion]
  exact (((((integrable_shifted_moment 2).const_mul 14400).add
    ((integrable_shifted_moment 3).const_mul 60)).sub
    ((integrable_shifted_moment 4).const_mul 316)).add
    ((integrable_shifted_moment 5).const_mul 32)).sub
    (integrable_shifted_moment 6) |>.div_const 864900

/-- Actual evaluation of the polynomial integral; no moment assumptions remain. -/
theorem integral_actual_trial_polynomial :
    (∫ x : ℝ in Ioi 0, trialPolynomial (x - 2) * (x ^ 2 * Real.exp (-x))) =
      16 / 155 := by
  let f (n : ℕ) (x : ℝ) := (x - 2) ^ n * (x ^ 2 * Real.exp (-x))
  have h (n : ℕ) : Integrable (f n) (volume.restrict (Ioi 0)) :=
    integrable_shifted_moment n
  have h23 : Integrable (fun x => 14400 * f 2 x + 60 * f 3 x)
      (volume.restrict (Ioi 0)) := (h 2 |>.const_mul 14400).add (h 3 |>.const_mul 60)
  have h234 : Integrable (fun x => 14400 * f 2 x + 60 * f 3 x - 316 * f 4 x)
      (volume.restrict (Ioi 0)) := h23.sub (h 4 |>.const_mul 316)
  have h2345 : Integrable
      (fun x => 14400 * f 2 x + 60 * f 3 x - 316 * f 4 x + 32 * f 5 x)
      (volume.restrict (Ioi 0)) := h234.add (h 5 |>.const_mul 32)
  simp_rw [weighted_trial_expansion]
  change (∫ x : ℝ in Ioi 0,
    (14400 * f 2 x + 60 * f 3 x - 316 * f 4 x + 32 * f 5 x - f 6 x) / 864900) = _
  rw [integral_div, integral_sub h2345 (h 6),
    integral_add h234 (h 5 |>.const_mul 32), integral_sub h23 (h 4 |>.const_mul 316),
    integral_add (h 2 |>.const_mul 14400) (h 3 |>.const_mul 60)]
  simp only [integral_const_mul, f]
  obtain ⟨_, _, m2, m3, m4, m5, m6⟩ := actual_shifted_moments
  rw [m2, m3, m4, m5, m6]
  exact moment_arithmetic

/-- The rational factor stays between zero and one on the entire real line. -/
theorem fraction_between_zero_one (y : ℝ) :
    0 ≤ y ^ 2 / (60 + y ^ 2) ∧ y ^ 2 / (60 + y ^ 2) ≤ 1 := by
  have hd : (0 : ℝ) < 60 + y ^ 2 := by positivity
  constructor
  · exact div_nonneg (sq_nonneg y) hd.le
  · apply (div_le_one hd).2
    linarith

/-- Actual rational integrability, using a bounded factor times the Gamma density. -/
theorem integrable_actual_fraction :
    IntegrableOn (fun x : ℝ =>
      ((x - 2) ^ 2 / (60 + (x - 2) ^ 2)) * (x ^ 2 * Real.exp (-x))) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ =>
      ((x - 2) ^ 2 / (60 + (x - 2) ^ 2)) * (x ^ 2 * Real.exp (-x))) := by
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        positivity
    · fun_prop
  refine (integrable_pow_exp_neg 2).mono' hc.aestronglyMeasurable ?_
  filter_upwards [] with x
  have hd : (0 : ℝ) ≤ x ^ 2 * Real.exp (-x) := by positivity
  obtain ⟨h0, h1⟩ := fraction_between_zero_one (x - 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hd)]
  exact mul_le_of_le_one_left hd h1

/-- The actual rational-integral estimate in the manuscript, without moment hypotheses. -/
theorem actual_fraction_integral_lower_bound :
    (16 / 155 : ℝ) ≤ ∫ x : ℝ in Ioi 0,
      ((x - 2) ^ 2 / (60 + (x - 2) ^ 2)) * (x ^ 2 * Real.exp (-x)) := by
  rw [← integral_actual_trial_polynomial]
  apply integral_mono integrable_actual_trial_polynomial integrable_actual_fraction
  intro x
  exact mul_le_mul_of_nonneg_right (trial_polynomial_le_fraction (x - 2)) (by positivity)

/-- Integrability of the actual `g` integrand in the negative trial. -/
theorem integrable_actual_trial_integrand :
    IntegrableOn (fun x : ℝ => bernoulliRatio (x - 2) * (x ^ 2 * Real.exp (-x)))
      (Ioi 0) := by
  have hmajor : IntegrableOn
      (fun x : ℝ => (x + 3) * (x ^ 2 * Real.exp (-x))) (Ioi 0) := by
    have heq : (fun x : ℝ => (x + 3) * (x ^ 2 * Real.exp (-x))) =
        (fun x => x ^ 3 * Real.exp (-x) + 3 * (x ^ 2 * Real.exp (-x))) := by
      funext x
      ring
    rw [heq]
    exact (integrable_pow_exp_neg 3).add ((integrable_pow_exp_neg 2).const_mul 3)
  have hm : Measurable (fun x : ℝ =>
      bernoulliRatio (x - 2) * (x ^ 2 * Real.exp (-x))) := by
    exact (measurable_bernoulliRatio.comp (measurable_id.sub_const 2)).mul
      (by fun_prop)
  refine hmajor.mono' hm.aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have hd : (0 : ℝ) ≤ x ^ 2 * Real.exp (-x) := by positivity
  have hg := bernoulli_bounds (x - 2)
  have ha : |x - 2| ≤ x + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg.1 hd)]
  exact mul_le_mul_of_nonneg_right (by linarith [hg.2]) hd

/-- The actual trial integral from equation `eq:st18-t00024`. -/
def actualTrialIntegral : ℝ :=
  ∫ x : ℝ in Ioi 0, bernoulliRatio (x - 2) * (x ^ 2 * Real.exp (-x))

/-- The full analytic lower bound `I ≥ 47/31`, with all scalar integrals established. -/
theorem actual_trial_integral_lower_bound : (47 / 31 : ℝ) ≤ actualTrialIntegral := by
  let d (x : ℝ) := x ^ 2 * Real.exp (-x)
  let f (x : ℝ) := ((x - 2) ^ 2 / (60 + (x - 2) ^ 2)) * d x
  let l (x : ℝ) := d x - ((x - 2) * d x) / 2 + 5 * f x
  have hd : Integrable d (volume.restrict (Ioi 0)) := integrable_pow_exp_neg 2
  have h1 : Integrable (fun x => (x - 2) * d x) (volume.restrict (Ioi 0)) := by
    simpa only [pow_one, d, IntegrableOn] using integrable_shifted_moment 1
  have hf : Integrable f (volume.restrict (Ioi 0)) := integrable_actual_fraction
  have hsub : Integrable (fun x => d x - ((x - 2) * d x) / 2)
      (volume.restrict (Ioi 0)) := hd.sub (h1.div_const 2)
  have hl : Integrable l (volume.restrict (Ioi 0)) := hsub.add (hf.const_mul 5)
  have hcompare : (∫ x in Ioi 0, l x) ≤ actualTrialIntegral := by
    apply integral_mono hl integrable_actual_trial_integrand
    intro x
    have h := mul_le_mul_of_nonneg_right (bernoulli_rational_lower_bound (x - 2))
      (show 0 ≤ d x by dsimp [d]; positivity)
    convert h using 1
    dsimp [l, f, d]
    ring
  have heval : (∫ x in Ioi 0, l x) = 2 - 1 + 5 * ∫ x in Ioi 0, f x := by
    change (∫ x in Ioi 0, d x - ((x - 2) * d x) / 2 + 5 * f x) = _
    rw [integral_add hsub (hf.const_mul 5),
      integral_sub hd (h1.div_const 2), integral_div, integral_const_mul]
    obtain ⟨m0, m1, _, _, _, _, _⟩ := actual_shifted_moments
    simp only [pow_zero, one_mul] at m0
    simp only [pow_one] at m1
    change (∫ x in Ioi 0, x ^ 2 * Real.exp (-x)) -
      (∫ x in Ioi 0, (x - 2) * (x ^ 2 * Real.exp (-x))) / 2 +
      5 * ∫ x in Ioi 0, f x = _
    rw [m0, m1]
    norm_num
  have hfrac : (16 / 155 : ℝ) ≤ ∫ x in Ioi 0, f x := actual_fraction_integral_lower_bound
  rw [heval] at hcompare
  linarith

/-- The actual scalar expression for the trial is strictly negative. -/
theorem actual_trial_expression_negative : 48 - 32 * actualTrialIntegral < 0 :=
  negative_trial_strict actualTrialIntegral actual_trial_integral_lower_bound

end ActualMoments

section IntegralConsequences

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {y : Ω → ℝ}

/-- Integrability of the explicit polynomial follows from its five power terms. -/
theorem integrable_trialPolynomial
    (h2 : Integrable (fun x => y x ^ 2) μ)
    (h3 : Integrable (fun x => y x ^ 3) μ)
    (h4 : Integrable (fun x => y x ^ 4) μ)
    (h5 : Integrable (fun x => y x ^ 5) μ)
    (h6 : Integrable (fun x => y x ^ 6) μ) :
    Integrable (fun x => trialPolynomial (y x)) μ := by
  exact (((((h2.const_mul 14400).add (h3.const_mul 60)).sub
    (h4.const_mul 316)).add (h5.const_mul 32)).sub h6).div_const 864900

/-- Exact evaluation of the polynomial integral from explicitly supplied moments.

This theorem does not assert the moment evaluations for a Gaussian measure.
Those analytic evaluations are hypotheses, separately visible in its type. -/
theorem integral_trialPolynomial_of_moments
    (h2 : Integrable (fun x => y x ^ 2) μ)
    (h3 : Integrable (fun x => y x ^ 3) μ)
    (h4 : Integrable (fun x => y x ^ 4) μ)
    (h5 : Integrable (fun x => y x ^ 5) μ)
    (h6 : Integrable (fun x => y x ^ 6) μ)
    (m2 : (∫ x, y x ^ 2 ∂μ) = 8)
    (m3 : (∫ x, y x ^ 3 ∂μ) = 32)
    (m4 : (∫ x, y x ^ 4 ∂μ) = 176)
    (m5 : (∫ x, y x ^ 5 ∂μ) = 1136)
    (m6 : (∫ x, y x ^ 6 ∂μ) = 8576) :
    (∫ x, trialPolynomial (y x) ∂μ) = 16 / 155 := by
  have h23 : Integrable (fun x => 14400 * y x ^ 2 + 60 * y x ^ 3) μ :=
    (h2.const_mul 14400).add (h3.const_mul 60)
  have h234 : Integrable
      (fun x => 14400 * y x ^ 2 + 60 * y x ^ 3 - 316 * y x ^ 4) μ :=
    h23.sub (h4.const_mul 316)
  have h2345 : Integrable
      (fun x => 14400 * y x ^ 2 + 60 * y x ^ 3 - 316 * y x ^ 4 + 32 * y x ^ 5) μ :=
    h234.add (h5.const_mul 32)
  unfold trialPolynomial
  rw [integral_div, integral_sub h2345 h6,
    integral_add h234 (h5.const_mul 32), integral_sub h23 (h4.const_mul 316),
    integral_add (h2.const_mul 14400) (h3.const_mul 60)]
  simp only [integral_const_mul, m2, m3, m4, m5, m6]
  exact moment_arithmetic

/-- Integrating the square-completion estimate with its integrability requirements. -/
theorem integral_fraction_ge_of_moments
    (h2 : Integrable (fun x => y x ^ 2) μ)
    (h3 : Integrable (fun x => y x ^ 3) μ)
    (h4 : Integrable (fun x => y x ^ 4) μ)
    (h5 : Integrable (fun x => y x ^ 5) μ)
    (h6 : Integrable (fun x => y x ^ 6) μ)
    (hf : Integrable (fun x => y x ^ 2 / (60 + y x ^ 2)) μ)
    (m2 : (∫ x, y x ^ 2 ∂μ) = 8)
    (m3 : (∫ x, y x ^ 3 ∂μ) = 32)
    (m4 : (∫ x, y x ^ 4 ∂μ) = 176)
    (m5 : (∫ x, y x ^ 5 ∂μ) = 1136)
    (m6 : (∫ x, y x ^ 6 ∂μ) = 8576) :
    (16 / 155 : ℝ) ≤ ∫ x, y x ^ 2 / (60 + y x ^ 2) ∂μ := by
  rw [← integral_trialPolynomial_of_moments h2 h3 h4 h5 h6 m2 m3 m4 m5 m6]
  exact integral_mono (integrable_trialPolynomial h2 h3 h4 h5 h6) hf
    (fun x => trial_polynomial_le_fraction (y x))

end IntegralConsequences

end UnforcedLeray.GaussianTrial
