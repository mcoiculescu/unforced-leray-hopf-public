import UnforcedLeray.Short.PartIIIb.MixedReturn

/-!
# Proof of `MR_Crossing` (target `mrCrossing`; source: `the November 2 reference manuscript`, lines 5768-5774)

Write `f(z) = 1 - e^{-z}`, so `f(-1) = 1 - e < 0` and `f(1) = 1 - e^{-1} > 0`.
Let `δ > 0` with `δ ≤ e - 1` and `δ ≤ 1 - e^{-1}`. Uniform convergence `d_n → f` on `[-1,1]`
gives, for large `n`, `d_n(-1) < f(-1) + δ ≤ 0` and `d_n(1) > f(1) - δ ≥ 0`. The intermediate
value theorem on `[-1,1]` gives a zero `w_n`, and `w_n ≠ ±1` because `d_n(±1) ≠ 0`.

Choose such zeros `z_n` for large `n`. For `0 < ε ≤ 1`, put `m = min (1 - e^{-ε}) (e^{ε} - 1) > 0`.
If `|z_n| ≥ ε`, monotonicity of `exp` gives `|f(z_n)| ≥ m`. But `|f(z_n)| = |d_n(z_n) - f(z_n)| < m`
for large `n`, by uniform convergence. Hence `|z_n| < ε` eventually, so `z_n → 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

open Filter Topology

theorem mrCrossing : UnforcedLeray.Short.PartIIIb.MR_Crossing := by
  intro d hcont hunif
  obtain ⟨δ, hδpos, hδ1, hδ2⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.exp 1 - 1 ∧ δ ≤ 1 - Real.exp (-1) := by
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    have hei : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact ⟨min (Real.exp 1 - 1) (1 - Real.exp (-1)), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  have hE := (Metric.tendstoUniformlyOn_iff.mp hunif) δ hδpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hE
  have hzero : ∀ n, N ≤ n → ∃ w : ℝ, w ∈ Set.Ioo (-1 : ℝ) 1 ∧ d n w = 0 := by
    intro n hn
    have hb := hN n hn
    have hm1 := hb (-1) (Set.left_mem_Icc.mpr (by norm_num))
    have hp1 := hb 1 (Set.right_mem_Icc.mpr (by norm_num))
    simp only [Real.dist_eq, neg_neg] at hm1 hp1
    have hneg : d n (-1) < 0 := by
      have := (abs_lt.mp hm1).1
      linarith
    have hpos : 0 < d n 1 := by
      have := (abs_lt.mp hp1).2
      linarith
    have hmem : (0 : ℝ) ∈ Set.Icc (d n (-1)) (d n 1) := ⟨le_of_lt hneg, le_of_lt hpos⟩
    obtain ⟨w, hw, hdw⟩ :=
      intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) (hcont n) hmem
    have hw1 : w ≠ -1 := by
      intro h
      subst h
      linarith
    have hw2 : w ≠ 1 := by
      intro h
      subst h
      linarith
    exact ⟨w, ⟨lt_of_le_of_ne hw.1 (Ne.symm hw1), lt_of_le_of_ne hw.2 hw2⟩, hdw⟩
  choose! g hg using hzero
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ n in atTop, |g n| < ε := by
    intro ε hε hε1
    have hexp1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hexp2 : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
    have hm : 0 < min (1 - Real.exp (-ε)) (Real.exp ε - 1) :=
      lt_min (by linarith) (by linarith)
    have hU := (Metric.tendstoUniformlyOn_iff.mp hunif) _ hm
    filter_upwards [hU, eventually_ge_atTop N] with n hUn hnN
    obtain ⟨hgI, hgd⟩ := hg n hnN
    have hbd := hUn (g n) (Set.Ioo_subset_Icc_self hgI)
    simp only [hgd, Real.dist_eq, sub_zero] at hbd
    have hmle1 : min (1 - Real.exp (-ε)) (Real.exp ε - 1) ≤ 1 - Real.exp (-ε) :=
      min_le_left _ _
    have hmle2 : min (1 - Real.exp (-ε)) (Real.exp ε - 1) ≤ Real.exp ε - 1 :=
      min_le_right _ _
    have hlt := abs_lt.mp hbd
    by_contra hcon0
    have hcon : ε ≤ |g n| := not_lt.mp hcon0
    rcases le_total 0 (g n) with h0 | h0
    · rw [abs_of_nonneg h0] at hcon
      have hle : Real.exp (-g n) ≤ Real.exp (-ε) := Real.exp_le_exp.mpr (by linarith)
      linarith [hlt.2]
    · rw [abs_of_nonpos h0] at hcon
      have hle : Real.exp ε ≤ Real.exp (-g n) := Real.exp_le_exp.mpr (by linarith)
      linarith [hlt.1]
  refine ⟨g, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [key (min ε 1) (lt_min hε one_pos) (min_le_right _ _)] with n hn
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le hn (min_le_left _ _)
  · filter_upwards [eventually_ge_atTop N] with n hn
    exact hg n hn

end UnforcedLeray.Short.PartIIIb
