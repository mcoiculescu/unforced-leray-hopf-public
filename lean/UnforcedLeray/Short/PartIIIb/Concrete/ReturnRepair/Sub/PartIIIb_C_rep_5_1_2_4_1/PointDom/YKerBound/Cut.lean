import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YKerBound.Dil
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Coeff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz.Cut

/-!
# `PDYKerBound` helpers (5): the cutoff profiles at the normalized radius

Source `the November 2 reference manuscript` 3700-3712, 4180-4186.

At `r = 1` with `t = νR² ∈ (0, 1]`, the cutoff `c(r) = χ̂(νR²/r²)` and the stream coefficient
`F(r) = χ̂'(νR²/r²)(-2νR²/r³)/r` and their first two derivatives are bounded by a constant
depending only on `sup_{[0,1]} |χ̂^{(j)}|`, `j ≤ 3` (explicit formulas of
`tcc_deriv_C0`, ..., `tcc_deriv_deriv_F0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ykb_stream_of_young {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) : IsStreamCutoff χ :=
  ⟨hχ.smooth, hχ.one, hχ.zero, hχ.range⟩

theorem ykb_cbounds {t x1 x2 x3 M : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h1 : |x1| ≤ M)
    (h2 : |x2| ≤ M) (h3 : |x3| ≤ M) :
    |-2 * t * x1| ≤ 2 * M ∧ |6 * t * x1 + 4 * t ^ 2 * x2| ≤ 10 * M ∧
      |8 * t * x1 + 4 * (t * t) * x2| ≤ 12 * M ∧
      |40 * t * x1 + 44 * t ^ 2 * x2 + 8 * t ^ 3 * x3| ≤ 92 * M := by
  have hp1 : |t * x1| ≤ M := by
    rw [abs_mul, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_right ht1 (abs_nonneg x1); linarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht3 : t ^ 3 ≤ 1 := by nlinarith
  have hp2 : |t ^ 2 * x2| ≤ M := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_right ht2 (abs_nonneg x2); linarith
  have hp3 : |t ^ 3 * x3| ≤ M := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_right ht3 (abs_nonneg x3); linarith
  obtain ⟨a1, b1⟩ := abs_le.1 hp1
  obtain ⟨a2, b2⟩ := abs_le.1 hp2
  obtain ⟨a3, b3⟩ := abs_le.1 hp3
  have e2 : t * t * x2 = t ^ 2 * x2 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- **Cutoff bounds at `r = 1`.** -/
theorem ykb_cut {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (ν R : ℝ), 0 < ν → ν * R ^ 2 ≤ 1 →
      ContDiffAt ℝ 2 (tcC0 ν R χ) 1 ∧ ContDiffAt ℝ 2 (tcF0 ν R χ) 1 ∧
      |tcC0 ν R χ 1| ≤ 1 ∧ |deriv (tcC0 ν R χ) 1| ≤ A ∧
      |deriv (deriv (tcC0 ν R χ)) 1 + deriv (tcC0 ν R χ) 1 / 1| ≤ A ∧
      |tcF0 ν R χ 1| ≤ A ∧ |deriv (tcF0 ν R χ) 1| ≤ A ∧
      |deriv (deriv (tcF0 ν R χ)) 1 + deriv (tcF0 ν R χ) 1 / 1| ≤ A := by
  have hs := ykb_stream_of_young hχ
  obtain ⟨d0, d1, d2, c1, c2, c3⟩ := tcc_smooth χ hs
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn (c1.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn (c2.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨M3, hM3⟩ := isCompact_Icc.exists_bound_of_continuousOn (c3.continuousOn (s := Icc (0 : ℝ) 1))
  set M := |M1| + |M2| + |M3| with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨104 * M, by positivity, fun ν R hν ht => ?_⟩
  set t := ν * R ^ 2 with htdef
  have ht0 : 0 ≤ t := by positivity
  have hmem : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht⟩
  have hx1 : |deriv χ t| ≤ M := by
    have := hM1 t hmem; rw [Real.norm_eq_abs] at this
    have := le_abs_self M1; have := abs_nonneg M2; have := abs_nonneg M3; linarith
  have hx2 : |deriv (deriv χ) t| ≤ M := by
    have := hM2 t hmem; rw [Real.norm_eq_abs] at this
    have := le_abs_self M2; have := abs_nonneg M1; have := abs_nonneg M3; linarith
  have hx3 : |deriv (deriv (deriv χ)) t| ≤ M := by
    have := hM3 t hmem; rw [Real.norm_eq_abs] at this
    have := le_abs_self M3; have := abs_nonneg M1; have := abs_nonneg M2; linarith
  obtain ⟨b1, b2, b3, b4⟩ := ykb_cbounds ht0 ht hx1 hx2 hx3
  have et : ν * (R ^ 2 / 1 ^ 2) = t := by rw [htdef]; ring
  have hC0 := tcc_deriv_C0 χ d0 ν R 1 one_ne_zero
  have hC1 := tcc_deriv_deriv_C0 χ d0 d1 ν R 1 one_pos
  have hF0 := tcc_tcF0_eq χ ν R 1
  have hF1 := tcc_deriv_F0 χ d1 ν R 1 one_pos
  have hF2 := tcc_deriv_deriv_F0 χ d1 d2 ν R 1 one_pos
  simp only [et, one_pow, div_one] at hC0 hC1 hF0 hF1 hF2
  refine ⟨tcle_c0_smooth hs ν R one_ne_zero, tcle_f0_smooth hs ν R one_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tcC0
    rw [et]
    obtain ⟨r0, r1⟩ := hχ.range t
    rw [abs_of_nonneg r0]; exact r1
  · rw [hC0]; linarith
  · rw [div_one, hC1, hC0]
    have : |6 * t * deriv χ t + 4 * t ^ 2 * deriv (deriv χ) t + -2 * t * deriv χ t| ≤
        |6 * t * deriv χ t + 4 * t ^ 2 * deriv (deriv χ) t| + |-2 * t * deriv χ t| :=
      abs_add_le _ _
    linarith
  · rw [hF0]; linarith
  · rw [hF1]; linarith
  · rw [div_one, hF2, hF1]
    have : |-(40 * t * deriv χ t + 44 * t ^ 2 * deriv (deriv χ) t +
        8 * t ^ 3 * deriv (deriv (deriv χ)) t) +
        (8 * t * deriv χ t + 4 * (t * t) * deriv (deriv χ) t)| ≤
        |-(40 * t * deriv χ t + 44 * t ^ 2 * deriv (deriv χ) t +
        8 * t ^ 3 * deriv (deriv (deriv χ)) t)| +
        |8 * t * deriv χ t + 4 * (t * t) * deriv (deriv χ) t| := abs_add_le _ _
    rw [abs_neg] at this
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete

end
