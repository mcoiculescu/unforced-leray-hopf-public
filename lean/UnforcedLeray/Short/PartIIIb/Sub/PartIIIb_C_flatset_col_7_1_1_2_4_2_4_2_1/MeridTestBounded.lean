import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!
# `MeridTestBounded` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/4`)

Source of record `the November 2 reference manuscript`
lines 1684-1689: a band test is bounded. The band `Icc s0 s1 × Icc 0 c × Icc (-L) L` is compact,
and `q`-periodicity moves every point into `[0, c]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

theorem meridTestBounded : MeridTestBounded := by
  intro c hc g hg
  obtain ⟨s0, s1, L, hs0, hb⟩ := hg.band
  have hK : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : ContinuousOn g (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    hg.smooth.continuous.continuousOn
  have hcn : ContinuousOn (fun p => ‖g p‖) (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    continuous_norm.comp_continuousOn hcont
  obtain ⟨M0, hM0⟩ := (hK.image_of_continuousOn hcn).bddAbove
  -- each `q`-slice of `g` is `c`-periodic
  have hper : ∀ s η : ℝ, Function.Periodic (fun q : ℝ => g (s, q, η)) c :=
    fun s η q => hg.periodic (s, q, η)
  -- reduce any `q` into `[0, c]` by a whole number of periods
  have red : ∀ s η q : ℝ, ∃ q' : ℝ, 0 ≤ q' ∧ q' ≤ c ∧ g (s, q', η) = g (s, q, η) := by
    intro s η q
    have h1 : (⌊q / c⌋ : ℝ) ≤ q / c := Int.floor_le _
    have h2 : q / c < (⌊q / c⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 : (⌊q / c⌋ : ℝ) * c ≤ q := (le_div_iff₀ hc).1 h1
    have h4 : q < ((⌊q / c⌋ : ℝ) + 1) * c := (div_lt_iff₀ hc).1 h2
    have h5 : ((⌊q / c⌋ : ℝ) + 1) * c = (⌊q / c⌋ : ℝ) * c + c := by ring
    refine ⟨q - (⌊q / c⌋ : ℝ) * c, by linarith, by linarith, ?_⟩
    exact (hper s η).sub_int_mul_eq ⌊q / c⌋
  refine ⟨max M0 0, fun p => ?_⟩
  by_cases h0 : g p = 0
  · rw [h0, norm_zero]
    exact le_max_right _ _
  · obtain ⟨hp1, hp2⟩ := hb p h0
    obtain ⟨q', hq0, hqc, hgq⟩ := red p.1 p.2.2 p.2.1
    have hgq' : g (p.1, q', p.2.2) = g p := hgq
    have hmem : (p.1, q', p.2.2) ∈ Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) :=
      ⟨hp1, ⟨hq0, hqc⟩, (abs_le.1 hp2).1, (abs_le.1 hp2).2⟩
    calc ‖g p‖ = ‖g (p.1, q', p.2.2)‖ := by rw [hgq']
      _ ≤ M0 := hM0 (Set.mem_image_of_mem (fun p => ‖g p‖) hmem)
      _ ≤ max M0 0 := le_max_left _ _

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
