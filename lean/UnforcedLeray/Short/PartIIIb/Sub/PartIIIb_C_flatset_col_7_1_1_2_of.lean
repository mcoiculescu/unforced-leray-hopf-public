import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_of

/-!
# `SmoothForceClassical` from six source facts (decomposition of `PartIII-b:C/flatset/col/7/1/1/2`)

Source of record `the November 2 reference manuscript` 1650-1656, 1684-1689:
for a smooth compactly supported force `g`, `b = R₀ g` is the Duhamel integral
`∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ) dσ` (`B0225.R0_Ms_ae`, `R0_apply`, `R0_ae_eq`), which is a classical
field for `s > 0` (heat-kernel smoothing of a compactly supported smooth force), divergence free
(`R₀ = (μ - A₀)⁻¹P₀`), with `b ∈ H` near `s = 0`.

The weak gradient is the classical `cellGrad`.  The facts:

* `SFCRep` : a smooth, measurable, `q`-periodic representative of `R₀ g` with slice-wise bounds
  of `b` and `cellGrad b` for each `s > 0` (Duhamel smoothness + bridge from `IsBodyTransport`);
* `SFCGradMeas` : `cellGrad b` is jointly measurable (Mathlib `measurable_fderiv` on the open set
  `s > 0`);
* `SFCZero` : the zero-entrance clause (`b =ᵐ R₀ g ∈ Hsp c`);
* `SFCEnergy` : local finiteness of `∫ |b|² + |∇b|²` on `[s₁,s₂] × cell` (heat-kernel gradient
  bound / energy of the Duhamel integral);
* `SFCWeak` : classical gradient is the weak gradient on every slice (integration by parts on the
  cell, periodic in `q`, tests compactly supported in `η`);
* `SFCDiv` : divergence-freeness of the representative at every `s > 0` (`P₀` range).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 HasWeakCellDerivC)

/-- The classical cell gradient `∂_j b_i` (`j = 0` is `q`, `j = 1` is `η`) of a field on the chart. -/
def cellGrad (b : Chart → Fin 2 → ℂ) (p : Chart) (i j : Fin 2) : ℂ :=
  fderiv ℝ (fun x : ℝ × ℝ => b (p.1, x) i) p.2 (B0579.dir j)

/-- Hypotheses of the classical case (source 1650-1656, 1684-1689). -/
def ClassicalCtx (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c) : Prop :=
  0 < ν ∧ 0 < μ + 1 / 4 ∧
    NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) ∧
    IsSmoothForce c g

/-- A classical representative (vanishing for `s ≤ 0`, outside the support of the age measure):
measurable, `C^∞` on `s > 0`, `q`-periodic, with slice-wise bounds
of the field and its cell gradient. -/
def SmoothRep (c : ℝ) (b : Chart → Fin 2 → ℂ) : Prop :=
  (∀ i, Measurable fun p => b p i) ∧
  (∀ i, ContDiffOn ℝ ∞ (fun p => b p i) (Ioi (0 : ℝ) ×ˢ univ)) ∧
  (∀ s q η, 0 < s → b (s, (q + c, η)) = b (s, (q, η))) ∧
  (∀ s, 0 < s → ∃ C : ℝ, ∀ x : ℝ × ℝ, vnorm2 (b (s, x)) ≤ C ∧
    ∀ i j, ‖cellGrad b (s, x) i j‖ ≤ C) ∧
  (∀ p : Chart, p.1 ≤ 0 → b p = 0)

/-- **R** Smooth representative of `R₀ g` (source 1650-1656, 1684-1689). -/
def SFCRep : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∃ b : Chart → Fin 2 → ℂ, SmoothRep c b ∧ b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)

/-- **M** Measurability of the classical gradient. -/
def SFCGradMeas : Prop :=
  ∀ (c : ℝ) (b : Chart → Fin 2 → ℂ), SmoothRep c b → ∀ i j, Measurable fun p => cellGrad b p i j

/-- **Z** Zero entrance (source 3426-3430 clause: `b ∈ 𝓗` near `s = 0`). -/
def SFCZero : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤

/-- **E** Local energy finiteness (heat-kernel gradient bound). -/
def SFCEnergy : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (fun i j => cellGrad b p i j) ^ 2) < ⊤

/-- **W** The classical gradient is the weak gradient on every slice. -/
def SFCWeak : Prop :=
  ∀ (c : ℝ) (b : Chart → Fin 2 → ℂ), SmoothRep c b → ∀ s : ℝ, 0 < s → ∀ i j : Fin 2,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => cellGrad b (s, x) i j)

/-- **D** Divergence-freeness of the representative at every `s > 0` (source 1650-1656). -/
def SFCDiv : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ b : Chart → Fin 2 → ℂ, SmoothRep c b → b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g) →
      ∀ s : ℝ, 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c,
          (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0

theorem smoothForceClassical_of (hR : SFCRep) (hM : SFCGradMeas) (hZ : SFCZero)
    (hE : SFCEnergy) (hW : SFCWeak) (hD : SFCDiv) : SmoothForceClassical := by
  intro c ν μ hc hν hμ R0 hT g hg
  have hctx : ClassicalCtx c ν μ hc R0 g := ⟨hν, hμ, hT, hg⟩
  obtain ⟨b, hb, hbe⟩ := hR c ν μ hc R0 g hctx
  refine ⟨b, fun p i j => cellGrad b p i j, ?_, hbe⟩
  exact
    { measurable := hb.1
      gradMeasurable := hM c b hb
      energyLoc := hE c ν μ hc R0 g hctx b hb hbe
      zeroEntrance := hZ c ν μ hc R0 g hctx b hb hbe
      divFree := hD c ν μ hc R0 g hctx b hb hbe
      weakGrad := hW c b hb }

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
