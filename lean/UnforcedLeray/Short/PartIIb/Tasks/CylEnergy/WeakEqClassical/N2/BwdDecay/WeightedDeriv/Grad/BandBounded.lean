import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!

is bounded on a band `[s, t] × ℝ × [a, b]`.

Source: `the November 2 reference manuscript` lines 2100-2105.

Reduce `x.1` modulo `c` into `[0, c]` by periodicity, then use compactness of
`[s, t] × [0, c] × [a, b]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem bandBounded : UnforcedLeray.Short.IIb.BandBounded := by
  intro c s t a b G hc hG hper
  have hK : IsCompact (Icc s t ×ˢ (Icc 0 c ×ˢ Icc a b) : Set (ℝ × B0579.Plane)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hGK : ContinuousOn (fun z : ℝ × B0579.Plane => G z.1 z.2)
      (Icc s t ×ˢ (Icc 0 c ×ˢ Icc a b)) :=
    hG.mono (fun z hz => ⟨hz.1, mem_univ _⟩)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGK
  refine ⟨C, fun r hr x hx => ?_⟩
  set k : ℤ := ⌊x.1 / c⌋ with hk
  have hfl1 : (k : ℝ) ≤ x.1 / c := Int.floor_le _
  have hfl2 : x.1 / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hA : (k : ℝ) * c ≤ x.1 := (le_div_iff₀ hc).1 hfl1
  have hB : x.1 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hfl2
  have hB' : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
  have hy0 : 0 ≤ x.1 - (k : ℝ) * c := by linarith
  have hyc : x.1 - (k : ℝ) * c ≤ c := by linarith
  have hp : Function.Periodic (fun u : ℝ => G r (u, x.2)) c :=
    fun u => hper r hr (u, x.2)
  have hshift : G r (x.1 - (k : ℝ) * c, x.2) = G r x := by
    have h := hp.sub_int_mul_eq (x := x.1) k
    simpa using h
  have hmem : (r, (x.1 - (k : ℝ) * c, x.2)) ∈ Icc s t ×ˢ (Icc 0 c ×ˢ Icc a b) :=
    ⟨hr, ⟨⟨hy0, hyc⟩, hx⟩⟩
  have hbound := hC (r, (x.1 - (k : ℝ) * c, x.2)) hmem
  simp only at hbound
  rw [hshift, Real.norm_eq_abs] at hbound
  exact hbound

end UnforcedLeray.Short.IIb
