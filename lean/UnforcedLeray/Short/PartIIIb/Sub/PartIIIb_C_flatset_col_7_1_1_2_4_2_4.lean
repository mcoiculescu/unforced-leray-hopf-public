import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_org

/-!
# `SFCDuhamelGrad` from the pointwise Duhamel identity and differentiation under the integral
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/4`)

Source `the November 2 reference manuscript`
1650-1656, 1684-1689, 3426-3430.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Pointwise upgrade of the ae Duhamel identity (source 1650-1656, 1684-1689): `b` is `C^∞` on
`s > 0` (`SmoothRep`) and `causalHeat c ν μ (sfcGp f')` is continuous on `s > 0` (the Duhamel integral
of the smooth, bounded, `q`-periodic datum `Gp` on `[s₀, s]`, `ν > 0`), and `ageμ c (-3/2)` charges
every open subset of `s > 0`; so the ae identity holds at every `(s, x)`, `s > 0`. -/
def SFCDuhamelEverywhere : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
        (∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i : Fin 2,
          b p i = (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i) →
        ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ, ∀ i : Fin 2,
          b (s, x) i = (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, x)) i

/-- Differentiation under the `σ`-integral (source 3426-3430): for the smooth (`σ ≥ s₀ > 0`
supported, bounded, `q`-periodic) datum `Gp` of a lift `f'` of a smooth force, with `ν > 0`,
`∂_j` of the causal heat at `s > 0` is the integral of `∂_j` of the heat (dominated convergence;
the integrand is dominated by `C (s-σ)^{-1/2}` times an `L¹` function of `σ`, or via the L²
contraction of `P₀`). -/
def SFCCausalHeatDiff : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
      ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ, ∀ i j : Fin 2,
        fderiv ℝ (fun y : ℝ × ℝ =>
            (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, y)) i) x
            (B0579.dir j) =
          ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ (μ : ℂ) *
            fderiv ℝ (fun y : ℝ × ℝ =>
              (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
                (fun z => UnforcedLeray.B0220.periodize c (sfcGp hc f') (σ, z)) y) i) x
              (B0579.dir j)

theorem sfcDuhamelGrad_of (hE : SFCDuhamelEverywhere) (hD : SFCCausalHeatDiff) :
    SFCDuhamelGrad := by
  intro c ν μ hc R0 g hctx b hb hae f' hlift hD' s hs x i j
  have hfun : (fun y : ℝ × ℝ => b (s, y) i) = fun y : ℝ × ℝ =>
      (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, y)) i :=
    funext fun y => hE c ν μ hc R0 g hctx b hb hae f' hlift hD' s hs y i
  unfold cellGrad
  simp only
  rw [hfun]
  exact hD c ν μ hc R0 g hctx f' hlift s hs x i j
end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
