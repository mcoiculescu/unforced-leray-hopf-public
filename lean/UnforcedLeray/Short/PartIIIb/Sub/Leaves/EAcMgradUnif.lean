import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Mgrad

/-!
# `PartIII-b:C/inst/10/3` leaf E1b: uniform bound on `∇p_j` (source 4964-4966, 4978)

`p_j = -a⁻³ e^{-|x_j|²/(2a)}` with `a = ageA ν s ≥ 1`. The pointwise bound `mg_mgrad_bound`
from `Mgrad.lean` is `a⁻³ e^{-|x_j|²/(2a)} · 2|x_j|/a`; here `a ≥ 1` removes the powers of `a`,
the exponent is compared with `e^{-|x_j|²/(4a)}`, and `|x_j| ≤ (1+|x_j|²)²`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Sup norm squared is at most the Euclidean square `sq2`. -/
lemma mu_norm_sq_le (y : ℝ × ℝ) : ‖y‖ ^ 2 ≤ sq2 y := by
  unfold sq2
  rw [Prod.norm_def]
  have h1 : ‖y.1‖ ^ 2 = y.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖y.2‖ ^ 2 = y.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rcases le_total ‖y.1‖ ‖y.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg y.1]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg y.2]

/-- `sq2` is nonnegative. -/
lemma mu_sq2_nonneg (y : ℝ × ℝ) : 0 ≤ sq2 y := by
  unfold sq2; positivity

/-- Leaf E1b (source 4964-4966, 4978): uniform bound on the meridional gradient of `p_j`. -/
theorem mgradPjUnif : MgradPjUnif := by
  refine ⟨2, by norm_num, ?_⟩
  intro ν s hν hν1 hs _ j x
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hmain := mg_mgrad_bound ν s ha j x
  have hn0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hQ : 0 ≤ sq2 (xj ν j x) := mu_sq2_nonneg _
  have hk3 : (ageA ν s ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hE : Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s))
      ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg hQ ha.le]
  have hA : 2 * ‖xj ν j x‖ / ageA ν s ≤ 2 * ‖xj ν j x‖ := div_le_self (by positivity) ha1
  have hnonneg : 0 ≤ 2 * ‖xj ν j x‖ / ageA ν s := div_nonneg (by positivity) ha.le
  have hE4 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have h1 : (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
      (2 * ‖xj ν j x‖ / ageA ν s))
      ≤ 1 * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 * ‖xj ν j x‖)) :=
    mul_le_mul hk3 (mul_le_mul hE hA hnonneg hE4)
      (mul_nonneg (Real.exp_pos _).le hnonneg) zero_le_one
  have hn2 := mu_norm_sq_le (xj ν j x)
  have hnS2 : ‖xj ν j x‖ ≤ (1 + sq2 (xj ν j x)) ^ 2 := by
    nlinarith [sq_nonneg (‖xj ν j x‖ - 1 / 2), hn2, hQ, sq_nonneg (sq2 (xj ν j x))]
  have h3 := mul_le_mul_of_nonneg_right hnS2 hE4
  calc ‖mgrad (pj ν s j) x‖
      ≤ (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
          (2 * ‖xj ν j x‖ / ageA ν s)) := hmain
    _ ≤ 1 * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 * ‖xj ν j x‖)) := h1
    _ = 2 * (‖xj ν j x‖ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by ring
    _ ≤ 2 * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by
        nlinarith [h3]

end UnforcedLeray.Short.PartIIIb.Concrete
