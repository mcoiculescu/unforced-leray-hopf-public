import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

lemma final_ineq (ε u Q ρo z2 B C Λ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 0 < u) (huB : u ≤ B)
    (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hB : 1 ≤ B) (hρ : 0 ≤ ρo) (hρu : ρo * u ≤ 1) (hC : 0 < C)
    (hΛ : 1 ≤ Λ) (hz : 0 ≤ z2) :
    2 * ε * (Λ * C * (ε ^ 5 * (u * Q) ^ 5) + 2 * C * (ε ^ 7 * (u * Q) ^ 7) +
      C * (ρo * ε ^ 5 + z2 * ε ^ 6) * (u * Q) ^ 6) ≤
      (2 * Λ + 8) * C * B ^ 9 * ε ^ 6 * (1 + z2) * u ^ 5 := by
  have hB0 : 0 ≤ B := by linarith
  have hε0 := hε.le
  have e8 : ε ^ 8 ≤ ε ^ 6 := pow_le_pow_of_le_one hε0 hε1 (by norm_num)
  have e7 : ε ^ 7 ≤ ε ^ 6 := pow_le_pow_of_le_one hε0 hε1 (by norm_num)
  have Q5 : Q ^ 5 ≤ B ^ 9 := (pow_le_pow_left₀ hQ hQB 5).trans (pow_le_pow_right₀ hB (by norm_num))
  have Q6 : Q ^ 6 ≤ B ^ 9 := (pow_le_pow_left₀ hQ hQB 6).trans (pow_le_pow_right₀ hB (by norm_num))
  have X7 : u ^ 2 * Q ^ 7 ≤ B ^ 9 := by
    have : u ^ 2 * Q ^ 7 ≤ B ^ 2 * B ^ 7 :=
      mul_le_mul (pow_le_pow_left₀ hu.le huB 2) (pow_le_pow_left₀ hQ hQB 7) (by positivity) (by positivity)
    calc _ ≤ _ := this
      _ = B ^ 9 := by ring
  have X6 : u * Q ^ 6 ≤ B ^ 9 := by
    have : u * Q ^ 6 ≤ B * B ^ 6 :=
      mul_le_mul huB (pow_le_pow_left₀ hQ hQB 6) (by positivity) hB0
    calc _ ≤ _ := this
      _ = B ^ 7 := by ring
      _ ≤ B ^ 9 := pow_le_pow_right₀ hB (by norm_num)
  have hε6 : 0 ≤ ε ^ 6 := by positivity
  have hu5 : 0 ≤ u ^ 5 := by positivity
  have eq : 2 * ε * (Λ * C * (ε ^ 5 * (u * Q) ^ 5) + 2 * C * (ε ^ 7 * (u * Q) ^ 7) +
      C * (ρo * ε ^ 5 + z2 * ε ^ 6) * (u * Q) ^ 6) =
      2 * Λ * C * ε ^ 6 * u ^ 5 * Q ^ 5 + 4 * C * ε ^ 8 * (u ^ 5 * (u ^ 2 * Q ^ 7)) +
      2 * C * ε ^ 6 * (ρo * u) * (u ^ 5 * Q ^ 5 * Q) + 2 * C * ε ^ 7 * z2 * (u ^ 5 * (u * Q ^ 6)) := by
    ring
  rw [eq]
  have t1 : 2 * Λ * C * ε ^ 6 * u ^ 5 * Q ^ 5 ≤ 2 * Λ * C * ε ^ 6 * u ^ 5 * B ^ 9 := by gcongr
  have t2 : 4 * C * ε ^ 8 * (u ^ 5 * (u ^ 2 * Q ^ 7)) ≤ 4 * C * ε ^ 6 * (u ^ 5 * B ^ 9) := by gcongr
  have t3 : 2 * C * ε ^ 6 * (ρo * u) * (u ^ 5 * Q ^ 5 * Q) ≤ 2 * C * ε ^ 6 * 1 * (u ^ 5 * B ^ 9) := by
    have : Q ^ 5 * Q = Q ^ 6 := by ring
    have h : u ^ 5 * Q ^ 5 * Q ≤ u ^ 5 * B ^ 9 := by
      calc u ^ 5 * Q ^ 5 * Q = u ^ 5 * Q ^ 6 := by ring
        _ ≤ _ := by gcongr
    gcongr
  have t4 : 2 * C * ε ^ 7 * z2 * (u ^ 5 * (u * Q ^ 6)) ≤ 2 * C * ε ^ 6 * z2 * (u ^ 5 * B ^ 9) := by gcongr
  have hfin : 0 ≤ C * ε ^ 6 * u ^ 5 * B ^ 9 := by positivity
  nlinarith [mul_nonneg hfin hz, mul_nonneg hfin (by linarith : 0 ≤ Λ - 1)]

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
