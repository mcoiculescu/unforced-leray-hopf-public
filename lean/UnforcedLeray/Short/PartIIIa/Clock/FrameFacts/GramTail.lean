import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramTail.Bound

/-!
# Part III-a, task `PartIII-a:T21/c1/b/2`: off-diagonal Gram tail (SP 2894-2895)

`Σ_{k≠0} ∫ λ_i(y) e_j(y₁ + kd, y₂) dy = O(d^{-2})`: each cross term is at most
`K/(1+|kd|)² ≤ K/(kd)²` by `gramCross_bound`, and `Σ_{k≠0} 1/k² < ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 2** (SP 2894-2895): the off-diagonal Gram tail is `O(d^{-2})`. -/
theorem perGramTail (κ : PlanarFrameKernels) : PerGramTail κ := by
  unfold PerGramTail
  obtain ⟨K, hK⟩ := gramCross_bound κ
  have K0 : 0 ≤ K := by
    have h0 := hK 0 0 0
    have hn := norm_nonneg (∫ y : ℝ × ℝ, κ.lamP 0 y * κ.e 0 (y.1, y.2))
    simp only [abs_zero, add_zero, one_pow, div_one] at h0
    linarith
  have hS : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine ⟨K * ∑' k : ℤ, 1 / (k : ℝ) ^ 2, 1, fun d hd i j => ?_⟩
  have hdpos : 0 < d := by linarith
  have hterm : ∀ k : ℤ, ‖(if k = 0 then (0 : ℂ) else gramTerm κ d i j k)‖ ≤
      K / d ^ 2 * (1 / (k : ℝ) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk]
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hb := hK i j ((k : ℝ) * d)
      have hgt : gramTerm κ d i j k = ∫ y : ℝ × ℝ, κ.lamP i y * κ.e j (y.1 + (k : ℝ) * d, y.2) := rfl
      rw [hgt]
      have hkd : (0 : ℝ) < ((k : ℝ) * d) ^ 2 := by
        have : (k : ℝ) * d ≠ 0 := mul_ne_zero hkR hdpos.ne'
        positivity
      calc ‖∫ y : ℝ × ℝ, κ.lamP i y * κ.e j (y.1 + (k : ℝ) * d, y.2)‖
          ≤ K / (1 + |(k : ℝ) * d|) ^ 2 := hb
        _ ≤ K / ((k : ℝ) * d) ^ 2 := by
            apply div_le_div_of_nonneg_left K0 hkd
            nlinarith [sq_abs ((k : ℝ) * d), abs_nonneg ((k : ℝ) * d)]
        _ = K / d ^ 2 * (1 / (k : ℝ) ^ 2) := by
            field_simp
  have hnorm : Summable (fun k : ℤ => ‖(if k = 0 then (0 : ℂ) else gramTerm κ d i j k)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm (hS.mul_left _)
  calc ‖∑' k : ℤ, (if k = 0 then (0 : ℂ) else gramTerm κ d i j k)‖
      ≤ ∑' k : ℤ, ‖(if k = 0 then (0 : ℂ) else gramTerm κ d i j k)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℤ, K / d ^ 2 * (1 / (k : ℝ) ^ 2) :=
        hnorm.tsum_le_tsum hterm (hS.mul_left _)
    _ = K / d ^ 2 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2 := tsum_mul_left
    _ = (K * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) / d ^ 2 := by ring

end UnforcedLeray.Short.IIIa
