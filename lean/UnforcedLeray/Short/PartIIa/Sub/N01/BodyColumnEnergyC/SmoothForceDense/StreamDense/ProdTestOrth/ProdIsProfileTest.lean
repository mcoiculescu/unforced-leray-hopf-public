import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3_2

/-!
# `ProdIsProfileTest` (`PartII-a:N01/9/1/1/3/2/1`), source lines 1684-1689

The product test `θ(s) ψ(q,η)` with `θ` a smooth bump supported in `(0,∞)` and `ψ` a cylinder test
is a profile test: smooth, `c`-periodic in `q` (since `ψ` is), and supported in a band
`s0 ≤ s ≤ s1`, `|η| ≤ R` with `s0 > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01.Sub

/-- A compactly supported bump `θ` with `tsupport θ ⊆ (0,∞)` vanishes outside some `[s0,s1]`,
`0 < s0`. -/
theorem prodTest_sBand {θ : ℝ → ℝ} (hθ : IsSBump θ) :
    ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ s : ℝ, θ s ≠ 0 → s ∈ Icc s0 s1 := by
  obtain ⟨_, hc, hsub⟩ := hθ
  by_cases hne : (tsupport θ).Nonempty
  · obtain ⟨a, ha, hmin⟩ :=
      hc.isCompact.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨b, hb, hmax⟩ :=
      hc.isCompact.exists_isMaxOn hne continuous_id.continuousOn
    refine ⟨a, b, hsub ha, fun s hs => ?_⟩
    have hmem : s ∈ tsupport θ := subset_tsupport θ hs
    exact ⟨isMinOn_iff.1 hmin s hmem, isMaxOn_iff.1 hmax s hmem⟩
  · refine ⟨1, 1, one_pos, fun s hs => ?_⟩
    exact absurd ⟨s, subset_tsupport θ hs⟩ hne

/-- `θ(s)ψ(q,η)` is a profile test. -/
theorem prodIsProfileTest : UnforcedLeray.Short.PartIIa.N01.Sub.ProdIsProfileTest := by
  intro c θ ψ hθ hψ
  obtain ⟨s0, s1, hs0, hband⟩ := prodTest_sBand hθ
  obtain ⟨R, hR⟩ := hψ.bounded
  refine ⟨?_, ?_, ⟨s0, s1, R, hs0, ?_⟩⟩
  · unfold prodFn
    exact (hθ.1.comp contDiff_fst).mul (hψ.smooth.comp contDiff_snd)
  · intro p
    have hp := hψ.periodic (p.2.1, p.2.2)
    simp only [prodFn, Prod.mk_add_mk, add_zero] at hp ⊢
    rw [hp]
  · intro p hp
    simp only [prodFn] at hp
    have hθ' : θ p.1 ≠ 0 := left_ne_zero_of_mul hp
    have hψ' : ψ p.2 ≠ 0 := right_ne_zero_of_mul hp
    exact ⟨hband p.1 hθ', not_lt.1 (fun h => hψ' (hR p.2 h))⟩

end UnforcedLeray.Short.PartIIa.N01.Sub
