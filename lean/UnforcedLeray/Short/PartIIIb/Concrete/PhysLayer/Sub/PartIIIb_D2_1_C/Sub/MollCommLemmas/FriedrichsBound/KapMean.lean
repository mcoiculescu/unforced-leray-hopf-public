import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_9

/-!
# `kapIntegrable`: the Friedrichs kernel is integrable

Source `the November 2 reference manuscript` lines 1556-1583.
`ρ.normed volume` is smooth with compact support, hence so is `kap ρ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem kapIntegrable : KapIntegrable := by
  intro ρ
  have hs : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed
  have hc : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  have hcf : HasCompactSupport (fderiv ℝ (ρ.normed volume)) := hc.fderiv ℝ
  have hcont : Continuous (kap ρ) := by
    unfold kap kerDv
    have h1 : Continuous (fderiv ℝ (ρ.normed volume)) := hs.continuous_fderiv one_ne_zero
    have h2 : Continuous fun z : ℝ × Space => fderiv ℝ (ρ.normed volume) z (0, z.2) :=
      h1.clm_apply (continuous_const.prodMk continuous_snd)
    exact (continuous_const.mul hs.continuous).add h2
  have hsupp : HasCompactSupport (kap ρ) := by
    refine HasCompactSupport.intro (K := tsupport (ρ.normed volume) ∪
      tsupport (fderiv ℝ (ρ.normed volume))) (hc.union hcf) ?_
    intro z hz
    simp only [mem_union, not_or] at hz
    have h1 := image_eq_zero_of_notMem_tsupport hz.1
    have h2 := image_eq_zero_of_notMem_tsupport hz.2
    unfold kap kerDv
    rw [h1, h2]
    simp
  exact hcont.integrable_of_hasCompactSupport hsupp

end UnforcedLeray.Short.PartIIIb.Concrete
