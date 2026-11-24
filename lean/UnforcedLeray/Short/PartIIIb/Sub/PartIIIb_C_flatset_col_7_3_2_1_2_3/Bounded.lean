import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3

/-!
# Smooth band tests are bounded (task `PartIII-b:C/flatset/col/7/3/2/1/2/3/3`)

Source `the November 2 reference manuscript` 1650-1656.  A smooth meridional test
`f` is continuous, `c`-periodic in `q`, and vanishes off `s ∈ [s₀,s₁]`, `|η| ≤ L`.  Its norm is
bounded on the compact box `[s₀,s₁] × [0,c] × [-L,L]`, and periodic reduction of `q` into
`(0,c]` (`periodic_reduceIoc_eq`) moves every point into that box.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)

theorem merid_test_bounded : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.MeridTestBounded := by
  intro c hc f hf
  obtain ⟨s0, s1, L, hs0, hband⟩ := hf.band
  have hcont : Continuous f := hf.smooth.continuous
  have hK : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M0 0, ?_⟩
  rintro ⟨s, q, η⟩
  by_cases hp : f (s, q, η) = 0
  · rw [hp, norm_zero]
    exact le_max_right _ _
  · obtain ⟨h1, h2⟩ := hband (s, q, η) hp
    have hq : UnforcedLeray.B0220.reduceIoc c q ∈ Ioc 0 c :=
      UnforcedLeray.B0220.reduceIoc_mem hc q
    have hmem : (s, UnforcedLeray.B0220.reduceIoc c q, η) ∈
        Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) :=
      ⟨h1, Ioc_subset_Icc_self hq, abs_le.mp h2⟩
    have heq : f (s, UnforcedLeray.B0220.reduceIoc c q, η) = f (s, q, η) :=
      UnforcedLeray.B0220.periodic_reduceIoc_eq f hf.periodic s q η
    have hb := hM0 _ hmem
    rw [heq] at hb
    exact hb.trans (le_max_left _ _)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
