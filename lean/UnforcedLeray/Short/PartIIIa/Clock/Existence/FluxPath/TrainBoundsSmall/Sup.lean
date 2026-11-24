import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Polynomial-times-exponential suprema (SP 460-467, absorbing the weight `⟨x⟩^m` into the tails)

For `l ≥ 0`: `(B₀ + l)^k e^{-bl/c}` and `(B₀ + l)^k e^{-bl²/D}` are bounded.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

theorem exists_poly_exp_sup (k : ℕ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {B0 : ℝ} (hB0 : 0 ≤ B0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℝ, 0 ≤ l → (B0 + l) ^ k * Real.exp (-(b * l / c)) ≤ M := by
  set β : ℝ := b / c with hβ
  have hβpos : 0 < β := div_pos hb hc
  refine ⟨(k.factorial : ℝ) / β ^ k * Real.exp (β * B0), by positivity, fun l hl => ?_⟩
  set t : ℝ := B0 + l with ht
  have ht0 : 0 ≤ t := by positivity
  have hexp : Real.exp (-(b * l / c)) = Real.exp (-(β * t)) * Real.exp (β * B0) := by
    rw [← Real.exp_add]
    congr 1
    rw [hβ, ht]
    field_simp
    ring
  have hu : (β * t) ^ k * Real.exp (-(β * t)) ≤ k.factorial := by
    have h1 := Real.pow_div_factorial_le_exp (β * t) (by positivity) k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    rw [div_le_iff₀ hf] at h1
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hpow : t ^ k * Real.exp (-(β * t)) ≤ (k.factorial : ℝ) / β ^ k := by
    rw [le_div_iff₀ (by positivity)]
    calc t ^ k * Real.exp (-(β * t)) * β ^ k = (β * t) ^ k * Real.exp (-(β * t)) := by
          rw [mul_pow]; ring
      _ ≤ _ := hu
  rw [hexp]
  calc t ^ k * (Real.exp (-(β * t)) * Real.exp (β * B0))
      = (t ^ k * Real.exp (-(β * t))) * Real.exp (β * B0) := by ring
    _ ≤ (k.factorial : ℝ) / β ^ k * Real.exp (β * B0) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

theorem exists_poly_gauss_sup (k : ℕ) {b D : ℝ} (hb : 0 < b) (hD : 0 < D) {B0 : ℝ}
    (hB0 : 0 ≤ B0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℝ, 0 ≤ l → (B0 + l) ^ k * Real.exp (-(b * l ^ 2 / D)) ≤ M := by
  obtain ⟨M1, hM1, h1⟩ := exists_poly_exp_sup k (b := 2 * b) (c := D) (by positivity) hD hB0
  refine ⟨Real.exp (b / D) * M1, by positivity, fun l hl => ?_⟩
  have hle : Real.exp (-(b * l ^ 2 / D)) ≤ Real.exp (b / D) * Real.exp (-(2 * b * l / D)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : b / D * (l - 1) ^ 2 ≥ 0 := by positivity
    have e : b / D + -(2 * b * l / D) + b * l ^ 2 / D = b / D * (l - 1) ^ 2 := by
      field_simp; ring
    linarith
  calc (B0 + l) ^ k * Real.exp (-(b * l ^ 2 / D))
      ≤ (B0 + l) ^ k * (Real.exp (b / D) * Real.exp (-(2 * b * l / D))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.exp (b / D) * ((B0 + l) ^ k * Real.exp (-(2 * b * l / D))) := by ring
    _ ≤ Real.exp (b / D) * M1 := mul_le_mul_of_nonneg_left (h1 l hl) (Real.exp_pos _).le

end UnforcedLeray.Short.IIIa.Exist
