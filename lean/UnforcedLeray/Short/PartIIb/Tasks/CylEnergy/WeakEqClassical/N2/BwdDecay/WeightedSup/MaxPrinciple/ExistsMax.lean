import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1_3

/-!
# `MpExistsMax` (SP 2100-2105): a positive supremum over the periodic strip is attained.

Compactness of `[s,t] × [0,c] × [-L,L]` and reduction of `q` modulo `c`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem mpExistsMax : MpExistsMax := by
  intro c s t G hc hst hcont hper ⟨L, hL⟩ ⟨r1, hr1, x1, hx1⟩
  -- reduction of `q` modulo `c`
  have red : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, 0 < G r x →
      ∃ x' : B0579.Plane, x' ∈ Icc 0 c ×ˢ Icc (-L) L ∧ G r x' = G r x := by
    intro r hr x hx
    have hxL : |x.2| < L := by
      by_contra h
      have := hL r hr x (not_lt.mp h)
      linarith
    have hf : Function.Periodic (fun q : ℝ => G r (q, x.2)) c := fun q => hper r hr (q, x.2)
    set n : ℤ := ⌊x.1 / c⌋ with hn
    refine ⟨(x.1 - n * c, x.2), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have h1 : (n : ℝ) ≤ x.1 / c := Int.floor_le _
      have := (le_div_iff₀ hc).mp h1
      simp only; linarith
    · have h1 : x.1 / c < n + 1 := Int.lt_floor_add_one _
      have := (div_lt_iff₀ hc).mp h1
      simp only; linarith
    · rw [abs_lt] at hxL
      exact ⟨by simp only; linarith, by simp only; linarith⟩
    · exact hf.sub_int_mul_eq n
  obtain ⟨x2, hx2, hGx2⟩ := red r1 hr1 x1 hx1
  have hK : IsCompact (Icc s t ×ˢ (Icc 0 c ×ˢ Icc (-L) L) : Set (ℝ × (ℝ × ℝ))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKc : ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2)
      (Icc s t ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    hcont.mono (prod_mono subset_rfl (subset_univ _))
  have hne : (Icc s t ×ˢ (Icc 0 c ×ˢ Icc (-L) L) : Set (ℝ × (ℝ × ℝ))).Nonempty :=
    ⟨(r1, x2), hr1, hx2⟩
  obtain ⟨z, hzK, hz⟩ := hK.exists_isMaxOn hne hKc
  refine ⟨z.1, hzK.1, z.2, fun r hr x => ?_⟩
  have hz1 : G r1 x2 ≤ G z.1 z.2 := isMaxOn_iff.mp hz (r1, x2) ⟨hr1, hx2⟩
  by_cases hx : 0 < G r x
  · obtain ⟨x', hx', hGx'⟩ := red r hr x hx
    rw [← hGx']
    exact isMaxOn_iff.mp hz (r, x') ⟨hr, hx'⟩
  · push_neg at hx
    linarith

end UnforcedLeray.Short.IIb
