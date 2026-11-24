import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Polynomial times Gaussian absorption (helper of `PsiProfileGaussBound`)

For `y : ℝ × ℝ` with sup norm `‖y‖` and `r = y₁² + y₂²`, the polynomial factor `(1 + ‖y‖)^N`
is absorbed by half of the Gaussian exponent: `(1+‖y‖)^N e^{-r/(4K)} ≤ C e^{-r/(8K)}`.
Source use: `PsiProfileGaussBound` (source 4991), with `sq2 y = y.1^2 + y.2^2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gauss_poly_absorb (N : ℕ) {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, ∀ y : ℝ × ℝ,
      (1 + ‖y‖) ^ N * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (4 * K)) ≤
        C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (8 * K)) := by
  refine ⟨(2 : ℝ) ^ (N - 1) * (2 + 2 ^ N * (8 * K) ^ N * (N.factorial : ℝ)), fun y => ?_⟩
  have ht0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have htle : ‖y‖ ≤ |y.1| + |y.2| := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs]; linarith [abs_nonneg y.2]
    · rw [Real.norm_eq_abs]; linarith [abs_nonneg y.1]
  have hsq : ‖y‖ ^ 2 ≤ 2 * (y.1 ^ 2 + y.2 ^ 2) := by
    have h1 : ‖y‖ ^ 2 ≤ (|y.1| + |y.2|) ^ 2 := pow_le_pow_left₀ ht0 htle 2
    nlinarith [sq_abs y.1, sq_abs y.2, sq_nonneg (|y.1| - |y.2|)]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (y.1 ^ 2 + y.2 ^ 2) / (8 * K) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hr_x : y.1 ^ 2 + y.2 ^ 2 = (8 * K) * x := by
    rw [hx]; field_simp
  have hE1 : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (4 * K)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; rw [hx]; field_simp; ring
  have hE2 : Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (8 * K)) = Real.exp (-x) := by
    congr 1; rw [hx]; ring
  rw [hE1, hE2]
  have hfact : x ^ N ≤ (N.factorial : ℝ) * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x hx0 N
    rw [div_le_iff₀ (by positivity)] at this
    linarith [mul_comm (Real.exp x) (N.factorial : ℝ)]
  have hpow : ‖y‖ ^ (2 * N) ≤ 2 ^ N * (8 * K) ^ N * x ^ N := by
    rw [pow_mul]
    calc (‖y‖ ^ 2) ^ N ≤ (2 * (y.1 ^ 2 + y.2 ^ 2)) ^ N :=
          pow_le_pow_left₀ (by positivity) hsq N
      _ = 2 ^ N * (8 * K) ^ N * x ^ N := by rw [hr_x]; simp only [mul_pow]; ring
  have hB : ‖y‖ ^ N ≤ 1 + 2 ^ N * (8 * K) ^ N * x ^ N := by
    have hB0 : 0 ≤ (2 : ℝ) ^ N * (8 * K) ^ N * x ^ N := by positivity
    rcases le_total ‖y‖ 1 with h | h
    · have : ‖y‖ ^ N ≤ 1 := pow_le_one₀ ht0 h
      linarith
    · have h2 : ‖y‖ ^ N ≤ ‖y‖ ^ (2 * N) := pow_le_pow_right₀ h (by omega)
      linarith
  have hA : (2 : ℝ) ^ N * (8 * K) ^ N * x ^ N ≤
      2 ^ N * (8 * K) ^ N * ((N.factorial : ℝ) * Real.exp x) :=
    mul_le_mul_of_nonneg_left (by linarith [hfact]) (by positivity)
  have hT : (1 + ‖y‖) ^ N ≤ (2 : ℝ) ^ (N - 1) *
      (2 + 2 ^ N * (8 * K) ^ N * ((N.factorial : ℝ) * Real.exp x)) := by
    have ha := add_pow_le (zero_le_one' ℝ) ht0 N
    rw [one_pow] at ha
    calc (1 + ‖y‖) ^ N ≤ (2 : ℝ) ^ (N - 1) * (1 + ‖y‖ ^ N) := ha
      _ ≤ (2 : ℝ) ^ (N - 1) *
          (2 + 2 ^ N * (8 * K) ^ N * ((N.factorial : ℝ) * Real.exp x)) :=
          mul_le_mul_of_nonneg_left (by linarith [hB, hA]) (by positivity)
  set E := Real.exp (-x) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1' : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp : Real.exp x * E = 1 := by rw [hE, ← Real.exp_add]; simp
  have hAnn : (0 : ℝ) ≤ 2 ^ N * (8 * K) ^ N * (N.factorial : ℝ) := by positivity
  have key : 2 * (E * E) + (2 : ℝ) ^ N * (8 * K) ^ N * (N.factorial : ℝ) * E ≤
      (2 + (2 : ℝ) ^ N * (8 * K) ^ N * (N.factorial : ℝ)) * E := by
    nlinarith [mul_le_mul_of_nonneg_left hE1' hE0.le]
  calc (1 + ‖y‖) ^ N * (E * E)
      ≤ (2 : ℝ) ^ (N - 1) *
          (2 + 2 ^ N * (8 * K) ^ N * ((N.factorial : ℝ) * Real.exp x)) * (E * E) :=
        mul_le_mul_of_nonneg_right hT (by positivity)
    _ = (2 : ℝ) ^ (N - 1) *
          (2 * (E * E) + 2 ^ N * (8 * K) ^ N * (N.factorial : ℝ) * (Real.exp x * E) * E) := by
        ring
    _ = (2 : ℝ) ^ (N - 1) *
          (2 * (E * E) + 2 ^ N * (8 * K) ^ N * (N.factorial : ℝ) * E) := by
        rw [hexp, mul_one]
    _ ≤ (2 : ℝ) ^ (N - 1) * ((2 + (2 : ℝ) ^ N * (8 * K) ^ N * (N.factorial : ℝ)) * E) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 : ℝ) ^ (N - 1) * (2 + 2 ^ N * (8 * K) ^ N * (N.factorial : ℝ)) * E := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
