import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Defs

/-!
# `ShellAbsorb`: polynomial factors are absorbed by exponential decay

Source `the November 2 reference manuscript`
lines 2545-2549 (arbitrary axial decay).  With `w = 1 + |t|` and `k = m + N`,
`(a w)^k / k! ≤ e^{a w} = e^a e^{a|t|}`, so `w^m e^{-a|t|} ≤ (k! e^a / a^k) w^{-N}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.Shell

/-- **`ShellAbsorb`** (source 2545-2549). -/
theorem shellAbsorb : ShellAbsorb := by
  intro a ha m N
  refine ⟨((m + N).factorial : ℝ) * Real.exp a / a ^ (m + N), fun t => ?_⟩
  have hw1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hw0 : 0 < 1 + |t| := by linarith
  have hexp := Real.pow_div_factorial_le_exp (x := a * (1 + |t|)) (mul_nonneg ha.le hw0.le) (m + N)
  have hfac : (0 : ℝ) < ((m + N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hak : 0 < a ^ (m + N) := pow_pos ha _
  have hwN : 0 < (1 + |t|) ^ N := pow_pos hw0 N
  rw [mul_pow, div_le_iff₀ hfac] at hexp
  have hsplit : Real.exp (a * (1 + |t|)) = Real.exp a * Real.exp (a * |t|) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.rpow_neg hw0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hwN,
    le_div_iff₀ hak]
  calc (1 + |t|) ^ m * Real.exp (-(a * |t|)) * (1 + |t|) ^ N * a ^ (m + N)
      = (a ^ (m + N) * (1 + |t|) ^ (m + N)) * Real.exp (-(a * |t|)) := by ring
    _ ≤ (Real.exp (a * (1 + |t|)) * ((m + N).factorial : ℝ)) * Real.exp (-(a * |t|)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = ((m + N).factorial : ℝ) * Real.exp a := by
        rw [hsplit, Real.exp_neg]
        field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.Shell
