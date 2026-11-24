import UnforcedLeray.Short.PartIIa.Sub.N02_4_11_2

/-!
# Part II-a, `Sub5` of `PartII-a:N02/4/11/2`: boundedness of a smooth band test

Source of record: `the November 2 reference manuscript`, lines 1744-1749, with
the standing period `c > 0` (lines 1637-1643).

`nzsBound : NzsBound` (`Sub/N02_4_11_2.lean`). The reduction of `q` to a period `[0, c)` uses
`Function.Periodic.exists_mem_Ico₀` (this is where `0 < c` enters: at `c = 0` periodicity is
vacuous and `φ(s) ψ(η) (1 + q²)` is an unbounded band test), and the bound on the compact box
`Icc s0 s1 ×ˢ Icc 0 c ×ˢ Icc (-L) L` uses `IsCompact.exists_bound_of_continuousOn`. Off the band
the test vanishes.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem nzsBound : NzsBound := by
  intro c hc f hf
  obtain ⟨s0, s1, L, _, hb⟩ := hf.band
  have hK : IsCompact (Icc s0 s1 ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.smooth.continuous.continuousOn
  refine ⟨max C 0, fun p => ?_⟩
  have hper : Function.Periodic (fun q : ℝ => f (p.1, q, p.2.2)) c :=
    fun q => hf.periodic (p.1, q, p.2.2)
  obtain ⟨q', hq', hfeq⟩ := hper.exists_mem_Ico₀ hc p.2.1
  have hfeq' : f p = f (p.1, q', p.2.2) := hfeq
  by_cases hx : p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L
  · have hmem : (p.1, q', p.2.2) ∈ Icc s0 s1 ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-L) L) :=
      ⟨hx.1, ⟨hq'.1, hq'.2.le⟩, abs_le.1 hx.2⟩
    rw [hfeq']
    exact (hC _ hmem).trans (le_max_left _ _)
  · have hz : f (p.1, q', p.2.2) = 0 := by
      by_contra hne
      obtain ⟨h1, h3⟩ := hb _ hne
      exact hx ⟨h1, h3⟩
    rw [hfeq', hz, norm_zero]
    exact le_max_right _ _

end UnforcedLeray.Short.PartIIa
