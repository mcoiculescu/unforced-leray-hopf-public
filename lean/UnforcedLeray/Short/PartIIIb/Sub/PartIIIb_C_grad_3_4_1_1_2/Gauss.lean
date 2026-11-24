import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp

/-!
# Gaussian absorption for the lattice envelope (source 5063-5079)

For `a ∈ [1, 2.1]` the Gaussian `e^{-(u²+η²)/(4a)}` has rate `≥ 1/8.4 > 1/9 = gradAlpha`, and a
monomial `|u|^p|η|^q` with `p + q ≤ 12 = gradK` is `≤ (1+|u|+|η|)^12`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradGaussAbsorb (a u η : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10) (p q : ℕ)
    (hpq : p + q ≤ 12) :
    |u| ^ p * |η| ^ q * Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) ≤ latticeW gradAlpha gradK u η := by
  unfold latticeW gradAlpha gradK
  have hB : (1 : ℝ) ≤ 1 + |u| + |η| := by
    have := abs_nonneg u; have := abs_nonneg η; linarith
  have h1 : |u| ^ p * |η| ^ q ≤ (1 + |u| + |η|) ^ (p + q) := by
    rw [pow_add]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (abs_nonneg _) (by have := abs_nonneg η; linarith) _
    · exact pow_le_pow_left₀ (abs_nonneg _) (by have := abs_nonneg u; linarith) _
    · positivity
    · positivity
  have h2 : (1 + |u| + |η|) ^ (p + q) ≤ (1 + |u| + |η|) ^ 12 :=
    pow_le_pow_right₀ hB hpq
  have h3 : Real.exp (-(u ^ 2 + η ^ 2) / (4 * a)) ≤ Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hr : 0 ≤ u ^ 2 + η ^ 2 := by positivity
    have ha : (0 : ℝ) < 4 * a := by linarith
    rw [div_le_iff₀ ha]
    nlinarith
  exact mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete
