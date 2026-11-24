import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!
# `MeridTestDeriv` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/3`)

Source of record `the November 2 reference manuscript`
lines 1650-1656: derivatives `∂_q`, `∂_η` of a band test are band tests.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem meridTestDeriv : MeridTestDeriv := by
  intro c g hg
  obtain ⟨s0, s1, L, hs0, hb⟩ := hg.band
  -- the derivative `∇g` is `c`-periodic in `q`
  have hfd : ∀ p : Profile, fderiv ℝ g (p.1, p.2.1 + c, p.2.2) = fderiv ℝ g p := by
    intro p
    have ha : ((p.1, p.2.1 + c, p.2.2) : Profile) = p + ((0 : ℝ), c, (0 : ℝ)) := by
      obtain ⟨s, q, η⟩ := p
      simp [add_comm]
    have hf : (fun x : Profile => g (x + ((0 : ℝ), c, (0 : ℝ)))) = g := by
      funext x
      obtain ⟨s, q, η⟩ := x
      have := hg.periodic (s, q, η)
      simpa using this
    rw [ha, ← fderiv_comp_add_right, hf]
  have hsmC : ContDiff ℝ ∞ (fderiv ℝ g) := hg.smooth.fderiv_right (m := ∞) (by simp)
  -- the closed band contains the support of `g`, so `∇g` vanishes outside the band
  have hB : IsClosed {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const)
  have hts : tsupport g ⊆ {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
    closure_minimal (fun p hp => hb p hp) hB
  have hzero : ∀ p : Profile, ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → fderiv ℝ g p = 0 := by
    intro p hp
    exact fderiv_of_notMem_tsupport ℝ (fun h => hp (hts h))
  -- every directional derivative of `g` is a band test
  have aux : ∀ v : Profile, IsMeridTest c (fun p => fderiv ℝ g p v) := by
    intro v
    refine ⟨?_, ?_, ?_⟩
    · exact hsmC.clm_apply contDiff_const
    · intro p
      show fderiv ℝ g (p.1, p.2.1 + c, p.2.2) v = fderiv ℝ g p v
      rw [hfd p]
    · refine ⟨s0, s1, L, hs0, fun p hp => ?_⟩
      by_contra h
      apply hp
      show fderiv ℝ g p v = 0
      rw [hzero p h, zero_apply]
  exact ⟨aux ((0 : ℝ), (1 : ℝ), (0 : ℝ)), aux ((0 : ℝ), (0 : ℝ), (1 : ℝ))⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
