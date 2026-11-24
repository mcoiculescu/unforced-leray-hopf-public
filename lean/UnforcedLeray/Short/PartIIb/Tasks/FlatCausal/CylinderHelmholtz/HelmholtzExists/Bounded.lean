import UnforcedLeray.Short.PartIIb.Sub.T12

/-!
# Boundedness of cylinder test weights

A continuous function on the plane which is `c`-periodic in `q` and vanishes for `|η|` large is
bounded: its values are attained on the compact strip `[0,c] × [-L,L]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

theorem bounded_of_periodic {c L : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hper : ∀ z : ℝ × ℝ, f (z.1 + c, z.2) = f z) (hL : ∀ z : ℝ × ℝ, L < |z.2| → f z = 0) :
    ∃ M : ℝ, ∀ z : ℝ × ℝ, ‖f z‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := c)).prod
    (isCompact_Icc (a := -L) (b := L))).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, fun z => ?_⟩
  by_cases hz : L < |z.2|
  · rw [hL z hz, norm_zero]
    exact le_max_right _ _
  · have hper' : Function.Periodic (fun q : ℝ => f (q, z.2)) c := fun q => hper (q, z.2)
    obtain ⟨y, hy, hfy⟩ := hper'.exists_mem_Ico₀ hc z.1
    have hzL : z.2 ∈ Icc (-L) L := abs_le.mp (not_lt.mp hz)
    have hmem : (y, z.2) ∈ Icc (0 : ℝ) c ×ˢ Icc (-L) L :=
      ⟨⟨hy.1, hy.2.le⟩, hzL⟩
    have h1 := hM (y, z.2) hmem
    have hzeq : f z = f (y, z.2) := by
      rw [← hfy]
    rw [hzeq]
    exact h1.trans (le_max_left _ _)

end UnforcedLeray.Short.IIb
