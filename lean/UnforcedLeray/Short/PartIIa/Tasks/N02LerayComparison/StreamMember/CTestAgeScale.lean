import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732
(weight `s^{-3/2}`). Target: `CTestAgeScale` (`Sub/N02_2.lean`): for every real `a`, the map
`F ↦ (p ↦ p.1 ^ a * F p)` sends complex band tests to complex band tests.

Template: `B0226.isProfileTest_ageScale` (`Units/B0226/Distrib.lean`), the real analogue.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Age scaling preserves complex band tests** (task `PartII-a:N02/2`): for every real exponent
`a`, `s ↦ s^a F` is again a complex band test. -/
theorem cTestAgeScale : UnforcedLeray.Short.PartIIa.CTestAgeScale := by
  intro c a F hF
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    obtain ⟨s0, s1, L, hs0, hb⟩ := hF.band
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((Real.contDiffAt_rpow_const_of_ne hp.ne').comp p contDiffAt_fst)).mul
        hF.smooth.contDiffAt
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      have hW : IsOpen {q : Profile | q.1 < s0} := isOpen_lt continuous_fst continuous_const
      filter_upwards [hW.mem_nhds (show p.1 < s0 by linarith [not_lt.1 hp])] with q hq
      have hFq : F q = 0 := by
        by_contra h
        exact absurd (hb q h).1.1 (not_le.2 hq)
      simp [hFq]
  · -- periodicity: the coefficient depends only on `p.1`
    intro p
    dsimp only
    rw [hF.periodic p]
  · -- band
    obtain ⟨s0, s1, L, hs0, hb⟩ := hF.band
    exact ⟨s0, s1, L, hs0, fun p hp => hb p (right_ne_zero_of_mul hp)⟩

end UnforcedLeray.Short.PartIIa

end
