import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_of

/-!
# `SFCEnergy` from the velocity half and the gradient half
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4`)

Source `the November 2 reference manuscript` 1684-1689, 3426-3430.  The strip energy
`∫ |b|² + |∇b|²` splits into the velocity part (from `b =ᵐ velC (R₀ g) ∈ Hsp`, weight
`s^(-3/2)` bounded below on `[s₁,s₂]`) and the gradient part (heat-kernel / Duhamel gradient
estimate for `R₀` on smooth compactly supported forces, `‖∇ e^{tΔ}g‖₂ ≤ ‖∇g‖₂`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- Velocity half of the strip energy (source 1684-1689): `b =ᵐ velC (R₀ g) ∈ Hsp`, and the weight
`s^(-3/2)` is bounded below on `[s₁,s₂]`. -/
def SFCEnergyV : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2) < ⊤

/-- Gradient half of the strip energy (source 1684-1689, 3426-3430): `∇b ∈ L²_loc((0,∞);L²)`,
by the Gaussian heat-kernel bound on `∇b = ∫ (σ/s)^μ ∇e^{ν(s-σ)Δ}g(σ)dσ`. -/
def SFCEnergyG : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (tnorm2 (fun i j => cellGrad b p i j) ^ 2) < ⊤

theorem sfcEnergy_of (hV : SFCEnergyV) (hG : SFCEnergyG) : SFCEnergy := by
  intro c ν μ hc R0 g hctx b hb hbe s₁ s₂ h1 h12
  have hv := hV c ν μ hc R0 g hctx b hb hbe s₁ s₂ h1 h12
  have hg := hG c ν μ hc R0 g hctx b hb hbe s₁ s₂ h1 h12
  have hmeas : Measurable fun p : Chart => ENNReal.ofReal (vnorm2 (b p) ^ 2) := by
    have : ∀ i, Measurable fun p : Chart => b p i := hb.1
    unfold vnorm2
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.pow_const ?_ 2
    refine Measurable.sqrt ?_
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (this i).norm.pow_const 2
  have hle : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (fun i j => cellGrad b p i j) ^ 2) =
      (∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2)) +
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (fun i j => cellGrad b p i j) ^ 2) := by
    rw [← lintegral_add_left hmeas]
    refine lintegral_congr (fun p => ?_)
    exact ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
  rw [hle]
  exact ENNReal.add_lt_top.2 ⟨hv, hg⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
