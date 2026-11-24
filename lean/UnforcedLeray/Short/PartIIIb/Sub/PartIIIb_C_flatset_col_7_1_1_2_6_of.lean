import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_of

/-!
# `SFCDiv` from an a.e.-`s` divergence identity and slice continuity
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6`)

Source `the November 2 reference manuscript` 1650-1656: `R₀ = (μ - A₀)⁻¹P₀` has
divergence-free range, so for a.e. `s` the slice of `b` integrates to zero against `∇ψ`; since
`s ↦ ∫ b(s,x)·∇ψ(x) dx` is continuous on `s > 0` (`b` jointly continuous there, `ψ` compactly
supported in `η`, `q`-periodicity on the bounded cell in `q`), it vanishes for every `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The slice divergence pairing `s ↦ ∫_cell b(s,x)·∇ψ(x) dx`. -/
def divPairing (c : ℝ) (b : Chart → Fin 2 → ℂ) (ψ : ℝ × ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ x in B0579.cell c,
    (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ))

/-- **A.e. form** (source 1650-1656): `P₀`-range divergence-freeness gives the weak slice divergence
for almost every `s > 0` (H-orthogonality of `R₀ g` to `∇(χ(s)ψ(x))`, then a.e. `s`). -/
def SFCDivAE : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ ψ, B0579.IsCylTest c ψ → ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), divPairing c b ψ s = 0

/-- **Continuity** of the slice pairing on `s > 0` for a smooth representative. -/
def SFCDivCont : Prop :=
  ∀ (c : ℝ) (b : Chart → Fin 2 → ℂ), SmoothRep c b → ∀ ψ, B0579.IsCylTest c ψ →
    ContinuousOn (divPairing c b ψ) (Ioi (0 : ℝ))

theorem sfcDiv_of (hAE : SFCDivAE) (hC : SFCDivCont) : SFCDiv := by
  intro c ν μ hc R0 g hctx b hb hbe s hs ψ hψ
  have hae := hAE c ν μ hc R0 g hctx b hb hbe ψ hψ
  have heq : divPairing c b ψ =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => (0 : ℂ) := hae
  have := Measure.eqOn_open_of_ae_eq heq isOpen_Ioi (hC c b hb ψ hψ) continuousOn_const hs
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
