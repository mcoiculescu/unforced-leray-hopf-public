import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.EBound.Weighted
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold.Fubini

/-!
# Part III-a, task `PartIII-a:T21/c1/b/3`: uniform `X_{m,d}` bound of `P_d e_i` (SP 2894-2897)

On the centred cell `|x₁| ≤ d/2`, `d ≥ 1`, every term `n ≠ 0` of `P_d e_i (x) = Σ_n e_i(x₁ + nd, x₂)`
has `(x₁ + nd)² ≥ ½(x₁² + n²/4)`, so `|P_d e_i(x)| ≤ M e^{-|x|²/16}` with `M` independent of `d ≥ 1`
(`Σ_n e^{-n²/64} < ∞`). The weighted norm is then absorbed by the Gaussian (`xNorm_le_of_gauss`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.IIIa

theorem summable_exp_int_sq : Summable (fun n : ℤ => Real.exp (-(n : ℝ) ^ 2 / (4 * 16))) := by
  have hs := (UnforcedLeray.Gaussian.summable_one_add_abs_int_rpow (s := 2) (by norm_num)).mul_left 128
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hs
  have hE := exp_neg_sq_mul_le (n : ℝ)
  have hpos : 0 < (1 + |(n : ℝ)|) ^ 2 := by positivity
  have hr : (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) = 1 / (1 + |(n : ℝ)|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  rw [hr, ← mul_div_assoc, mul_one, le_div_iff₀ hpos]
  linarith

/-- Pointwise Gaussian bound of the periodized growing vectors on the cell, uniform in `d ≥ 1`. -/
theorem perE_pointwise (κ : PlanarFrameKernels) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ d : ℝ, 1 ≤ d → ∀ (i : Fin 2) (x : ℝ × ℝ), x ∈ B0579.cell d →
      ‖perE κ d i x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  set S : ℝ := ∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / (4 * 16)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => (Real.exp_pos _).le
  refine ⟨|C| * S, by positivity, fun d hd i x hx => ?_⟩
  have hd0 : 0 < d := by linarith
  have hx1 : |x.1| ≤ d / 2 := by
    have h := hx
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at h
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hterm : ∀ n : ℤ, ‖κ.e i (x.1 + n * d, x.2)‖ ≤
      |C| * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(n : ℝ) ^ 2 / (4 * 16)) := by
    intro n
    have h1 := hC i (x.1 + n * d, x.2)
    have h2 : ‖κ.e i (x.1 + n * d, x.2)‖ ≤
        |C| * Real.exp (-((x.1 + n * d) ^ 2 + x.2 ^ 2) / 8) :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
    refine h2.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg C)
    by_cases hn : n = 0
    · subst hn
      simp only [Int.cast_zero, zero_mul, add_zero]
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    · have hN : 1 ≤ |(n : ℝ)| := by
        have := Int.one_le_abs hn
        exact_mod_cast this
      have hND : |(n : ℝ)| * d = |(n : ℝ) * d| := by rw [abs_mul, abs_of_pos hd0]
      have htri : |(n : ℝ) * d| ≤ |x.1 + n * d| + |x.1| := by
        calc |(n : ℝ) * d| = |(x.1 + n * d) - x.1| := by congr 1; ring
          _ ≤ |x.1 + n * d| + |x.1| := abs_sub _ _
      have hlow : |(n : ℝ)| * d / 2 ≤ |x.1 + n * d| := by
        nlinarith [mul_le_mul_of_nonneg_right hN hd0.le]
      have hsq : ((n : ℝ) * d) ^ 2 / 4 ≤ (x.1 + n * d) ^ 2 := by
        have h := pow_le_pow_left₀ (by positivity) hlow 2
        have e1 : (|(n : ℝ)| * d / 2) ^ 2 = ((n : ℝ) * d) ^ 2 / 4 := by
          rw [div_pow, mul_pow, sq_abs]; ring
        rw [e1, sq_abs] at h
        exact h
      have hx2 : x.1 ^ 2 ≤ d ^ 2 / 4 := by
        have := pow_le_pow_left₀ (abs_nonneg x.1) hx1 2
        rw [sq_abs, div_pow] at this
        linarith
      have hn2 : 1 ≤ (n : ℝ) ^ 2 := by
        have : 1 ≤ |(n : ℝ)| ^ 2 := by nlinarith
        rwa [sq_abs] at this
      have hd2 : 1 ≤ d ^ 2 := by nlinarith
      have hA : x.1 ^ 2 ≤ (x.1 + n * d) ^ 2 := by
        have : d ^ 2 / 4 ≤ ((n : ℝ) * d) ^ 2 / 4 := by
          rw [mul_pow]; nlinarith [sq_nonneg d]
        linarith
      have hB : (n : ℝ) ^ 2 / 4 ≤ (x.1 + n * d) ^ 2 := by
        have : (n : ℝ) ^ 2 / 4 ≤ ((n : ℝ) * d) ^ 2 / 4 := by
          rw [mul_pow]; nlinarith [sq_nonneg (n : ℝ)]
        linarith
      nlinarith [sq_nonneg x.2]
  have hsumE := summable_e_shift κ hd0 i x
  have hsumR : Summable (fun n : ℤ =>
      |C| * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(n : ℝ) ^ 2 / (4 * 16))) :=
    summable_exp_int_sq.mul_left _
  calc ‖perE κ d i x‖ ≤ ∑' n : ℤ, ‖κ.e i (x.1 + n * d, x.2)‖ := by
        unfold perE perSum
        exact norm_tsum_le_tsum_norm hsumE
    _ ≤ ∑' n : ℤ, |C| * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) *
          Real.exp (-(n : ℝ) ^ 2 / (4 * 16)) := hsumE.tsum_le_tsum hterm hsumR
    _ = (|C| * S) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
        rw [tsum_mul_left, hS]; ring

/-- **Leaf 3** (SP 2894-2895): uniform `X_{m,d}` bound of the periodized growing vectors. -/
theorem perEBound (κ : PlanarFrameKernels) : PerEBound κ := by
  intro m hm
  obtain ⟨M, hM0, hM⟩ := perE_pointwise κ
  obtain ⟨K, hK0, hK⟩ := xNorm_le_of_gauss (m := m) (by linarith)
  exact ⟨M * K, fun d hd i => hK d M (perE κ d i) hM0 fun x hx => hM d hd i x hx⟩

end UnforcedLeray.Short.IIIa
