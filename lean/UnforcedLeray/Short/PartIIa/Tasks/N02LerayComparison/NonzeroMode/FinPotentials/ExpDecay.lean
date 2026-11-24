import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Deriv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Decay

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- A finite family of positive numbers has a common positive lower bound. -/
theorem nzfp_lb_pos (M : Finset ℤ) (k : ℤ → ℝ) (hk : ∀ n ∈ M, 0 < k n) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n ∈ M, κ ≤ k n := by
  induction M using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert j M hj ih =>
    obtain ⟨κ, hκ, h⟩ := ih (fun n hn => hk n (Finset.mem_insert_of_mem hn))
    refine ⟨min κ (k j), lt_min hκ (hk j (Finset.mem_insert_self _ _)), ?_⟩
    intro n hn
    rcases Finset.mem_insert.1 hn with rfl | hn'
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h n hn')

/-- The mode factor `e^{2π i n q / c}` has modulus one. -/
theorem nzfp_exp_norm (c : ℝ) (n : ℤ) (q : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ) =
      ((2 * Real.pi * n * q / c : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Triangle inequality for a finite sum with termwise bounds. -/
theorem nzfp_sum_bound (M : Finset ℤ) (f : ℤ → ℂ) (a : ℤ → ℝ) (E : ℝ)
    (h : ∀ n ∈ M, ‖f n‖ ≤ a n * E) : ‖∑ n ∈ M, f n‖ ≤ (∑ n ∈ M, a n) * E := by
  rw [Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum h)

/-- Exponential weights with a smaller rate dominate those with a larger rate. -/
theorem nzfp_C_exp_le (C κ κ0 η : ℝ) (hκ : κ0 ≤ κ) :
    C * Real.exp (-κ * |η|) ≤ |C| * Real.exp (-κ0 * |η|) := by
  have h1 : Real.exp (-κ * |η|) ≤ Real.exp (-κ0 * |η|) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg η])
  calc C * Real.exp (-κ * |η|) ≤ |C| * Real.exp (-κ * |η|) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)
    _ ≤ |C| * Real.exp (-κ0 * |η|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)

/-- A directional derivative in the `η`-direction is bounded by the full derivative. -/
theorem nzfp_fderiv_01 (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    ‖fderiv ℝ f x ((0 : ℝ), (1 : ℝ))‖ ≤ ‖fderiv ℝ f x‖ := by
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  calc ‖fderiv ℝ f x ((0 : ℝ), (1 : ℝ))‖ ≤ ‖fderiv ℝ f x‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
        (fderiv ℝ f x).le_opNorm _
    _ ≤ ‖fderiv ℝ f x‖ * 1 := mul_le_mul_of_nonneg_left h01 (norm_nonneg _)
    _ = ‖fderiv ℝ f x‖ := mul_one _

theorem nzFpExpDecay : NzFpExpDecay := by
  intro c _ M φ hφ
  have hdn : ∀ n ∈ M, ∃ κ C : ℝ, 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖φ n x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ (φ n) x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ (fderiv ℝ (φ n)) x‖ ≤ C * Real.exp (-κ * |x.2|) :=
    fun n hn => nzmb_decay_norms (φ n) (hφ n hn)
  choose! κ C hκ hbd using hdn
  obtain ⟨κ0, hκ0, hle⟩ := nzfp_lb_pos M κ hκ
  have hA : ∀ n ∈ M, ∀ s η : ℝ, ‖φ n (s, η)‖ ≤ |C n| * Real.exp (-κ0 * |η|) := by
    intro n hn s η
    exact le_trans (hbd n hn (s, η)).1 (nzfp_C_exp_le (C n) (κ n) κ0 η (hle n hn))
  have hB : ∀ n ∈ M, ∀ s η : ℝ,
      ‖fderiv ℝ (φ n) (s, η) ((0 : ℝ), (1 : ℝ))‖ ≤ |C n| * Real.exp (-κ0 * |η|) := by
    intro n hn s η
    exact le_trans (nzfp_fderiv_01 (φ n) (s, η))
      (le_trans (hbd n hn (s, η)).2.1 (nzfp_C_exp_le (C n) (κ n) κ0 η (hle n hn)))
  have hφs : ∀ n ∈ M, ContDiff ℝ ∞ (φ n) := fun n hn => (hφ n hn).1
  refine ⟨κ0, ∑ n ∈ M, (1 + |nzk c n|) * |C n|, hκ0, fun p => ?_⟩
  have hE : 0 ≤ Real.exp (-κ0 * |p.2.2|) := (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_⟩
  · unfold nzModeSum
    refine nzfp_sum_bound M _ (fun n => (1 + |nzk c n|) * |C n|) _ ?_
    intro n hn
    simp only [norm_smul, nzfp_exp_norm, one_mul]
    exact le_trans (hA n hn p.1 p.2.2)
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _)
        (by linarith [abs_nonneg (nzk c n)])) hE)
  · rw [nzfp_pdQ_mode c M φ hφs p]
    unfold nzModeSum
    refine nzfp_sum_bound M _ (fun n => (1 + |nzk c n|) * |C n|) _ ?_
    intro n hn
    simp only [norm_smul, nzfp_exp_norm, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul]
    have hCE : 0 ≤ |C n| * Real.exp (-κ0 * |p.2.2|) := by positivity
    calc |nzk c n| * ‖φ n (p.1, p.2.2)‖
        ≤ |nzk c n| * (|C n| * Real.exp (-κ0 * |p.2.2|)) :=
          mul_le_mul_of_nonneg_left (hA n hn p.1 p.2.2) (abs_nonneg _)
      _ ≤ (1 + |nzk c n|) * |C n| * Real.exp (-κ0 * |p.2.2|) := by nlinarith [hCE]
  · rw [nzfp_pdEta_mode c M φ hφs p]
    unfold nzModeSum
    refine nzfp_sum_bound M _ (fun n => (1 + |nzk c n|) * |C n|) _ ?_
    intro n hn
    simp only [norm_smul, nzfp_exp_norm, one_mul]
    exact le_trans (hB n hn p.1 p.2.2)
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _)
        (by linarith [abs_nonneg (nzk c n)])) hE)

end UnforcedLeray.Short.PartIIa
