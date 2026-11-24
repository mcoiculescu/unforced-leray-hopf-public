import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3_2

/-!
# `ProdIsStreamFn` (`PartII-a:N01/9/1/1/3/2/2`), source lines 1684-1689

The product test `θ(s) ψ(q,η)` (cast to `ℂ`) is a stream function: smooth, `c`-periodic in `q`,
supported in `s0 ≤ s ≤ s1` and `|η| ≤ R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01.Sub

/-- A compactly supported bump `θ` with `tsupport θ ⊆ (0,∞)` vanishes outside some `[s0,s1]`,
`0 < s0`. -/
theorem prodStream_sBand {θ : ℝ → ℝ} (hθ : IsSBump θ) :
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

/-- `θ(s)ψ(q,η)` (cast to `ℂ`) is a stream function. -/
theorem prodIsStreamFn : UnforcedLeray.Short.PartIIa.N01.Sub.ProdIsStreamFn := by
  intro c θ ψ hθ hψ
  obtain ⟨s0, s1, hs0, hband⟩ := prodStream_sBand hθ
  obtain ⟨R, hR⟩ := hψ.bounded
  have hsm : ContDiff ℝ ∞ (fun p : UnforcedLeray.B0220.Profile => prodFn θ ψ p) :=
    (hθ.1.comp contDiff_fst).mul (hψ.smooth.comp contDiff_snd)
  have hper : ∀ p : UnforcedLeray.B0220.Profile,
      prodFn θ ψ (p.1, p.2.1 + c, p.2.2) = prodFn θ ψ p := by
    intro p
    have hp := hψ.periodic (p.2.1, p.2.2)
    simp only [prodFn, Prod.mk_add_mk, add_zero] at hp ⊢
    rw [hp]
  refine ⟨?_, ?_, ⟨s0, s1, R, hs0, ?_⟩⟩
  · exact Complex.ofRealCLM.contDiff.comp hsm
  · intro p
    show ((prodFn θ ψ (p.1, p.2.1 + c, p.2.2) : ℝ) : ℂ) = ((prodFn θ ψ p : ℝ) : ℂ)
    rw [hper p]
  · intro p hp
    have hz : prodFn θ ψ p = 0 := by
      by_contra hne
      simp only [prodFn] at hne
      have hθ' : θ p.1 ≠ 0 := left_ne_zero_of_mul hne
      have hψ' : ψ p.2 ≠ 0 := right_ne_zero_of_mul hne
      have h1 : p.1 ∈ Icc s0 s1 := hband p.1 hθ'
      have h2 : |p.2.2| ≤ R := not_lt.1 (fun h => hψ' (hR p.2 h))
      rcases hp with h | h | h
      · linarith [h1.1]
      · linarith [h1.2]
      · linarith
    simp only [hz, Complex.ofReal_zero]

end UnforcedLeray.Short.PartIIa.N01.Sub
