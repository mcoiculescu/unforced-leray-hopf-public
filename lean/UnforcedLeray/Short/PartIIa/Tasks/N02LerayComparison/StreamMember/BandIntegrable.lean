import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestAgeScale

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732
(weight `s^{-3/2}`). Target: `BandIntegrable` (`Sub/N02_2.lean`): for every complex band test `G`
(`IsCTest c G`), `G` and `s^{-3/2} G` are integrable on `cell c`.

Route: `G` is continuous and vanishes on `cell c` outside the compact box
`K = [s₀, s₁] × [0, c] × [-L, L]`, so it is integrable on `K` and hence on the cell
(`bai_first`). The weighted function is again a complex band test by `cTestAgeScale`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- A complex band test is integrable on `cell c` (helper for `bandIntegrable`). -/
theorem bai_first {c : ℝ} {G : Profile → ℂ} (hG : IsCTest c G) : IntegrableOn G (cell c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hG.band
  have hK : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hGc : Continuous G := hG.smooth.continuous
  have hcell : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  refine IntegrableOn.of_forall_sdiff_eq_zero (hGc.continuousOn.integrableOn_compact hK)
    hcell ?_
  intro x hx
  by_contra hne
  obtain ⟨h1, h2⟩ := hb x hne
  have hxc : x ∈ cell c := hx.1
  have hx2 : x.2.1 ∈ Ioc 0 c := hxc.2.1
  apply hx.2
  refine mk_mem_prod h1 (mk_mem_prod ⟨hx2.1.le, hx2.2⟩ ⟨?_, ?_⟩)
  · exact (abs_le.1 h2).1
  · exact (abs_le.1 h2).2

/-- Band tests are integrable on the cell, and so are their `s^{-3/2}`-weighted versions
(task `PartII-a:N02/2/5`). -/
theorem bandIntegrable : UnforcedLeray.Short.PartIIa.BandIntegrable := by
  intro c G hG
  exact ⟨bai_first hG, bai_first (cTestAgeScale c (-(3 / 2 : ℝ)) G hG)⟩

end UnforcedLeray.Short.PartIIa

end
