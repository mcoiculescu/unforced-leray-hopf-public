import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L2.Slices

/-!
# `SFCDuhamelGradRep` from `SFCDuhamelGrad` (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/3/org`)

Source `the November 2 reference manuscript`
3426-3430.  For `σ < s` the heat `e^{ν(s-σ)Δ}` is a Gaussian average (`planeHeat_congr_pt`), so in the
Duhamel gradient formula the datum `sfcGp hc f'` may be replaced by any `Gs` equal to it
`measureH`-a.e. (`ae_slices_of_measureH`: the periodized slices agree a.e. for a.e. `σ > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDuhamelGradRep_of_grad (hG : SFCDuhamelGrad) : SFCDuhamelGradRep := by
  intro c ν μ hc R0 g hctx b hb hae f' hlift hD Gs hGs s hs x i j
  rw [hG c ν μ hc R0 g hctx b hb hae f' hlift hD s hs x i j]
  have hν : 0 < ν := hctx.1
  have hS := ae_slices_of_measureH hc hGs
  have hne : ∀ᵐ σ : ℝ, σ ≠ s := (Set.countable_singleton s).ae_notMem volume
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hS, hne] with σ hσ hne' hmem
  rw [Set.uIoc_of_le hs.le] at hmem
  have hlt : σ < s := lt_of_le_of_ne hmem.2 hne'
  have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hlt)
  have hu : (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) =ᵐ[volume]
      (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) := by
    filter_upwards [hσ hmem.1] with z hz
    exact hz.symm
  have hfun : (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) y) i) =
      (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) y) i) := by
    funext y
    rw [planeHeat_congr_pt hθ hu y]
  simp only [hfun]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
