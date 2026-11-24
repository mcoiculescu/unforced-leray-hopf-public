import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_3_of
import UnforcedLeray.Units.B0226.Distrib
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# `flatProductTest` (leaf of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/3/1`)

Source `the November 2 reference manuscript` 1650-1656.  The product
`Φ = χ(s) s^{3/2} ψ(q,η)` is the age-scaling `ageScale (3/2)` of the profile test `χ(s) ψ(q,η)`
(`isProfileTest_ageScale`), and `cgrad 0 Φ ∈ L²(measureH c)` by `memLp_cgrad`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatProductTest : FlatProductTest := by
  intro c hc χ hχs hχc hχsupp ψ hψ
  -- the band of `χ` inside `(0,∞)`
  obtain ⟨s0, s1, hs0, hbd⟩ : ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ s : ℝ, χ s ≠ 0 → s ∈ Icc s0 s1 := by
    rcases (tsupport χ).eq_empty_or_nonempty with he | hne
    · refine ⟨1, 1, one_pos, fun s hs => ?_⟩
      exfalso
      apply hs
      have hns : s ∉ tsupport χ := by rw [he]; exact notMem_empty s
      exact image_eq_zero_of_notMem_tsupport hns
    · obtain ⟨a, ha, hamin⟩ := hχc.isCompact.exists_isMinOn hne continuousOn_id
      obtain ⟨b, hb, hbmax⟩ := hχc.isCompact.exists_isMaxOn hne continuousOn_id
      refine ⟨a, b, hχsupp ha, fun s hs => ?_⟩
      exact ⟨isMinOn_iff.1 hamin s (subset_tsupport χ hs),
        isMaxOn_iff.1 hbmax s (subset_tsupport χ hs)⟩
  obtain ⟨R, hR⟩ := hψ.band
  have hΨs : ContDiff ℝ ∞ (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) :=
    (hχs.comp contDiff_fst).mul
      (hψ.smooth.comp ((contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd)))
  have hΨp : UnforcedLeray.B0226.IsProfileTest c
      (fun p : UnforcedLeray.B0220.Profile => χ p.1 * ψ (p.2.1, p.2.2)) := by
    refine ⟨hΨs, ?_, ?_⟩
    · intro p
      show χ p.1 * ψ (p.2.1 + c, p.2.2) = χ p.1 * ψ (p.2.1, p.2.2)
      exact congrArg (fun t => χ p.1 * t) (hψ.periodic (p.2.1, p.2.2))
    · refine ⟨s0, s1, R, hs0, ?_⟩
      intro p hp
      have hp' : χ p.1 * ψ (p.2.1, p.2.2) ≠ 0 := hp
      refine ⟨hbd p.1 (left_ne_zero_of_mul hp'), ?_⟩
      by_contra hlt
      exact (right_ne_zero_of_mul hp') (hR (p.2.1, p.2.2) (not_le.1 hlt))
  refine ⟨⟨fun p => UnforcedLeray.B0226.ageScale (3 / 2) (fun p : UnforcedLeray.B0220.Profile =>
      χ p.1 * ψ (p.2.1, p.2.2)) p, UnforcedLeray.B0226.isProfileTest_ageScale (3 / 2) hΨp⟩,
    ?_, ?_⟩
  · intro p
    show p.1 ^ (3 / 2 : ℝ) * (χ p.1 * ψ (p.2.1, p.2.2)) = χ p.1 * p.1 ^ (3 / 2 : ℝ) * ψ (p.2.1, p.2.2)
    ring
  · exact UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad
      (ε := 0) (UnforcedLeray.B0226.isProfileTest_ageScale (3 / 2) hΨp)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
