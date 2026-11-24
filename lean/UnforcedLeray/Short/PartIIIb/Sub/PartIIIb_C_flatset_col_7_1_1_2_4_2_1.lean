import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_org

/-!
# `SFCDuhamel` from the lift and the Duhamel identity for a lift
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/1`)

Source `the November 2 reference manuscript`
1650-1656, 1684-1689, 3426-3430.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Every `g ∈ Hsp c` has a lift `f'` to the complex profile space (source 1650-1656): `p ↦ merC (g (cellPt c p))`
is in `L²(measureH c)` (cell-periodic extension, `cellPtH_aux`, `memLp_map_measure_iff`). -/
def SFCLiftEx : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (g : Hsp c),
    ∃ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f'

/-- Duhamel identity for any lift (source 1650-1656, 1684-1689, `B0225.R0_Ms_ae_causalHeat`):
`velC (R₀ g) = causalHeat c ν μ (sfcGp f')` ae for `ageμ c (-3/2)`. -/
def SFCDuhamelLift : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
      ∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i : Fin 2,
        NearInst.velC (R0 g) p i = (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i

theorem sfcDuhamel_of (hL : SFCLiftEx) (hD : SFCDuhamelLift) : SFCDuhamel := by
  intro c ν μ hc R0 g hctx b _hb hbe
  obtain ⟨f', hf'⟩ := hL c hc g
  refine ⟨f', hf', ?_⟩
  filter_upwards [hbe, hD c ν μ hc R0 g hctx f' hf'] with p h1 h2 i
  rw [h1]
  exact h2 i

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
