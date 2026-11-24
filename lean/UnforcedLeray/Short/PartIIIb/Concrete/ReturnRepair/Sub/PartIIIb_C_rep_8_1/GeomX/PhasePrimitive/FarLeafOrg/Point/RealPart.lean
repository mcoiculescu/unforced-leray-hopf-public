import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.Ineq

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

lemma rp_neg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

lemma real_part (C Λ ε ρo ρi ν c r z2 : ℝ) (hCpos : 0 < C) (hΛ1 : 1 ≤ Λ) (hν : 0 < ν)
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hxo : ρi ≤ r)
    (hg : 0 < (r - ρo) / ε) :
    2 * ε * (Λ * (C * ((r - ρo) / ε) ^ (-5 : ℝ)) + 2 * C * ((r - ρo) / ε) ^ (-7 : ℝ) +
      C * (ρo / ε + |z2|) * ((r - ρo) / ε) ^ (-6 : ℝ)) ≤
    (2 * Λ + 8) * C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ 9 * ε ^ 6 * (1 + |z2|) *
      r ^ (-5 : ℝ) := by
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := by linarith
  have hd : 0 < r - ρo := by linarith
  have eg : ∀ n : ℕ, ((r - ρo) / ε) ^ (-(n : ℝ)) = ε ^ n * (r⁻¹ * (r / (r - ρo))) ^ n := by
    intro n
    rw [rp_neg _ hg.le n, ← inv_pow, inv_div]
    have : r⁻¹ * (r / (r - ρo)) = (r - ρo)⁻¹ := by field_simp
    rw [this, div_pow, inv_pow, div_eq_mul_inv]
  have g5' : ((r - ρo) / ε) ^ (-5 : ℝ) = ε ^ 5 * (r⁻¹ * (r / (r - ρo))) ^ 5 := by
    rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num]; exact eg 5
  have g6' : ((r - ρo) / ε) ^ (-6 : ℝ) = ε ^ 6 * (r⁻¹ * (r / (r - ρo))) ^ 6 := by
    rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num]; exact eg 6
  have g7' : ((r - ρo) / ε) ^ (-7 : ℝ) = ε ^ 7 * (r⁻¹ * (r / (r - ρo))) ^ 7 := by
    rw [show (-7 : ℝ) = -((7 : ℕ) : ℝ) by norm_num]; exact eg 7
  have r5 : r ^ (-5 : ℝ) = (r⁻¹) ^ 5 := by
    rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, rp_neg r hrpos.le 5, inv_pow]
  rw [g5', g6', g7', r5]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹ := ⟨_, rfl⟩
  rw [← hBdef]
  have hρiρo : 0 < ρi - ρo := by linarith
  have n1 : 0 ≤ ν⁻¹ := by positivity
  have n2 : 0 ≤ ρi⁻¹ := by positivity
  have n3 : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith
  have huB : r⁻¹ ≤ B := by
    have h1 : r⁻¹ ≤ ρi⁻¹ := inv_anti₀ hρi hxo
    rw [hBdef]; linarith
  have hQB : r / (r - ρo) ≤ B := by
    have h1 : r / (r - ρo) ≤ ρi / (ρi - ρo) := by
      rw [div_le_div_iff₀ hd hρiρo]
      nlinarith [mul_nonneg hρo (sub_nonneg.2 hxo)]
    rw [hBdef, ← div_eq_mul_inv]
    linarith
  have hρu : ρo * r⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hrpos]; linarith
  have hfin := final_ineq ε r⁻¹ (r / (r - ρo)) ρo |z2| B C Λ hε hε1 (inv_pos.2 hrpos) huB
    (div_nonneg hrpos.le hd.le) hQB hB1 hρo hρu hCpos hΛ1 (abs_nonneg _)
  have hEeq : 2 * ε * (Λ * (C * (ε ^ 5 * (r⁻¹ * (r / (r - ρo))) ^ 5)) +
      2 * C * (ε ^ 7 * (r⁻¹ * (r / (r - ρo))) ^ 7) +
      C * (ρo / ε + |z2|) * (ε ^ 6 * (r⁻¹ * (r / (r - ρo))) ^ 6)) =
      2 * ε * (Λ * C * (ε ^ 5 * (r⁻¹ * (r / (r - ρo))) ^ 5) +
      2 * C * (ε ^ 7 * (r⁻¹ * (r / (r - ρo))) ^ 7) +
      C * (ρo * ε ^ 5 + |z2| * ε ^ 6) * (r⁻¹ * (r / (r - ρo))) ^ 6) := by
    field_simp
  rw [hEeq]
  exact hfin

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
