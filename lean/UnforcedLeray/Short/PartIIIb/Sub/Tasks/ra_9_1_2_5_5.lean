import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_5

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gaussLatticeSummable (P : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun j : ℤ => (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2)) := by
  have hexp : ∀ n : ℕ, (1 + (n:ℝ)) ^ P * Real.exp (-c * (n:ℝ))
      = ∑ m ∈ Finset.range (P+1), (P.choose m : ℝ) * ((n:ℝ)^m * Real.exp (-c * (n:ℝ))) := by
    intro n
    rw [show (1 + (n:ℝ)) = (n:ℝ) + 1 by ring, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [one_pow, mul_one]
    ring
  have hg : Summable (fun n : ℕ => (1 + (n:ℝ)) ^ P * Real.exp (-c * (n:ℝ))) := by
    simp_rw [hexp]
    exact summable_sum (fun m _ => (Real.summable_pow_mul_exp_neg_nat_mul m hc).mul_left (P.choose m : ℝ))
  have hbound : ∀ n : ℕ, (1 + (n:ℝ)) ^ P * Real.exp (-c * (n:ℝ)^2)
      ≤ (1 + (n:ℝ)) ^ P * Real.exp (-c * (n:ℝ)) := by
    intro n
    have hn : (n:ℝ) ≤ (n:ℝ)^2 := by
      have : n ≤ n^2 := Nat.le_self_pow (by norm_num) n
      exact_mod_cast this
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hn)]
  have hnat : Summable (fun n : ℕ => (1 + (n:ℝ)) ^ P * Real.exp (-c * (n:ℝ)^2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbound hg
  apply Summable.of_nat_of_neg
  · refine hnat.congr (fun n => ?_)
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
  · refine hnat.congr (fun n => ?_)
    have h1 : (((-(n:ℤ)) : ℤ) : ℝ) = -(n:ℝ) := by push_cast; ring
    rw [h1, abs_neg, abs_of_nonneg (Nat.cast_nonneg n), neg_sq]

end UnforcedLeray.Short.PartIIIb.Concrete
