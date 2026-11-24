import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- A finite family of `s`-bands has a common hull. -/
theorem nzfp_hull_fin (M : Finset ℤ) (Q : ℤ → ℝ × ℝ → Prop)
    (h : ∀ n ∈ M, ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ x : ℝ × ℝ, Q n x → x.1 ∈ Icc s0 s1) :
    ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ n ∈ M, ∀ x : ℝ × ℝ, Q n x → x.1 ∈ Icc s0 s1 := by
  induction M using Finset.induction_on with
  | empty => exact ⟨1, 0, one_pos, by simp⟩
  | @insert j M hj ih =>
    obtain ⟨s0, s1, h0, hI⟩ := ih (fun n hn => h n (Finset.mem_insert_of_mem hn))
    obtain ⟨t0, t1, u0, hJ⟩ := h j (Finset.mem_insert_self _ _)
    refine ⟨min s0 t0, max s1 t1, lt_min h0 u0, ?_⟩
    intro n hn x hx
    rcases Finset.mem_insert.1 hn with rfl | hn'
    · obtain ⟨a, b⟩ := hJ x hx
      exact ⟨le_trans (min_le_right _ _) a, le_trans b (le_max_right _ _)⟩
    · obtain ⟨a, b⟩ := hI n hn' x hx
      exact ⟨le_trans (min_le_left _ _) a, le_trans b (le_max_left _ _)⟩

theorem nzFpBand : NzFpBand := by
  intro c M φ ψ hφ hψ
  have hor : ∀ n ∈ M, ∃ s0 s1 : ℝ, 0 < s0 ∧
      ∀ x : ℝ × ℝ, (φ n x ≠ 0 ∨ ψ n x ≠ 0) → x.1 ∈ Icc s0 s1 := by
    intro n hn
    obtain ⟨s0, s1, h0, hA⟩ := hφ n hn
    obtain ⟨t0, t1, u0, hB⟩ := hψ n hn
    refine ⟨min s0 t0, max s1 t1, lt_min h0 u0, fun x hx => ?_⟩
    rcases hx with hx | hx
    · obtain ⟨a, b⟩ := hA x hx
      exact ⟨le_trans (min_le_left _ _) a, le_trans b (le_max_left _ _)⟩
    · obtain ⟨a, b⟩ := hB x hx
      exact ⟨le_trans (min_le_right _ _) a, le_trans b (le_max_right _ _)⟩
  obtain ⟨s0, s1, h0, hI⟩ := nzfp_hull_fin M (fun n x => φ n x ≠ 0 ∨ ψ n x ≠ 0) hor
  refine ⟨s0, s1, h0, fun p hp => ?_⟩
  have key : ∀ g : ℤ → ℝ × ℝ → ℂ, nzModeSum c M g p ≠ 0 → ∃ n ∈ M, g n (p.1, p.2.2) ≠ 0 := by
    intro g hg
    by_contra hcon
    push_neg at hcon
    apply hg
    unfold nzModeSum
    exact Finset.sum_eq_zero (fun n hn => by rw [hcon n hn, smul_zero])
  rcases hp with hp | hp
  · obtain ⟨n, hn, hne⟩ := key φ hp
    exact hI n hn (p.1, p.2.2) (Or.inl hne)
  · obtain ⟨n, hn, hne⟩ := key ψ hp
    exact hI n hn (p.1, p.2.2) (Or.inr hne)

end UnforcedLeray.Short.PartIIa
