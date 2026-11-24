import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_of

/-!
# `SFCDatumReg` from flat-projection regularity and the a.e.-class invariance of the plane heat
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1`)

Source `the November 2 reference manuscript`
lines 1650-1656, 1684-1689, 3426-3430.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Flat Leray regularity of smooth data (source 1650-1656, 1684-1689): for a lift `f'` of a smooth
compactly supported force `g` (smooth, `q`-periodic, support in `s ∈ [s₀, s₁]`, `|η| ≤ L`, `s₀ > 0`),
the flat projection `P₀ f'` (`PepsC 0 c f'`, orthogonal projection onto the exact solenoidal
subspace; it acts in `(q, η)` at fixed age) agrees `measureH`-a.e. with a continuous, bounded,
`c`-periodic-in-`q` profile `G` that vanishes for `σ < s₀'` for some `s₀' > 0`. -/
def FlatProjSmoothRegular : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (g : Hsp c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    IsSmoothForce c g → SFCLift g f' →
      ∃ G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
        Continuous G ∧
        (∀ σ q η, G (σ, (q + c, η)) = G (σ, (q, η))) ∧
        (∃ M : ℝ, ∀ p, ‖G p‖ ≤ M) ∧
        (∃ s0 : ℝ, 0 < s0 ∧ ∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0) ∧
        ((UnforcedLeray.Short.PartIIa.PepsC 0 c f' :
            UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c] G)

/-- The plane heat sees only the a.e.-class of its datum in `z` (Gaussian integral; source
1684-1689, 3426-3430): if `P₀ f' = G` `measureH`-a.e. and `G` is `q`-periodic, then for a.e. `σ > 0`
the heat of the periodized `sfcGp` equals the heat of `σ⁻¹ G(σ, ·)` at every positive time
`θ > 0` (Fubini on `measureH`-null sets, `ae_cell_measureH`, periodization reduces `q` into the
cell, the integrand differs on a null set of `z`).  Only `θ = ν (s - σ) > 0` is used (source
3426-3430); at `θ ≤ 0`, `planeHeat θ = id` and the identity would be pointwise, which is false. -/
def PlaneHeatAeDatum : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC),
    (∀ σ q η, G (σ, (q + c, η)) = G (σ, (q, η))) →
    ((UnforcedLeray.Short.PartIIa.PepsC 0 c f' :
        UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
      =ᵐ[UnforcedLeray.B0220.measureH c] G) →
    ∀ᵐ σ ∂(volume : Measure ℝ), 0 < σ → ∀ θ : ℝ, 0 < θ →
      UnforcedLeray.B0224.planeHeat θ
          (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) =
        UnforcedLeray.B0224.planeHeat θ (fun z => (((σ : ℝ) : ℂ)⁻¹) • G (σ, z))

theorem sfcDatumReg_of (h1 : FlatProjSmoothRegular) (h2 : PlaneHeatAeDatum) : SFCDatumReg := by
  intro c hc g f' hs hl
  obtain ⟨G, hc1, hper, hb, hs0, hae⟩ := h1 c hc g f' hs hl
  exact ⟨G, hc1, hper, hb, hs0, h2 c hc f' G hper hae⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
