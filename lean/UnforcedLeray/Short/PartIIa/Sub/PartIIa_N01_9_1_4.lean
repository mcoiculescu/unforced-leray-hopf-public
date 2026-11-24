import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1

/-!
# `PartII-a:N01/9/1/4` (decomposition): `EnergyClosure`

Source `the November 2 reference manuscript`
lines 3426-3430 (energy class closed under `L²` limits, null-set redefinition).

Route: (1) the Cauchy gradients converge in `L²(ageμ c (-1/2))` to a measurable `G`
(`EnergyGradLimit`, completeness); (2) `b_k → b := R₀(μ)g` in `L²(ageμ c (-3/2))`, with `b`
measurable and of finite global energy (`EnergyVelLimit`, bridge `𝓗`-norm to the `ageμ` norm,
`‖R₀‖ ≤ (Re μ + 1/4)⁻¹`); (3) `energyLoc` (`EnergyLimitLoc`), `divFreeAE` (`EnergyLimitDivFree`)
and `weakGradAE` (`EnergyLimitWeakGrad`) pass to the limit; `zeroEntrance` is the global finiteness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (tnorm2 vnorm2 HasWeakCellDerivC)

/-- `L²` convergence `b_k → b` in `L²(ageμ c (-3/2))` and `G_k → G` in `L²(ageμ c (-1/2))`. -/
def EnergyL2Limit (c : ℝ) (bk : ℕ → Chart → Fin 2 → ℂ) (Gk : ℕ → Chart → Fin 2 → Fin 2 → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) : Prop :=
  Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (vnorm2 (fun i => bk k p i - b p i) ^ 2)
      ∂(ageμ c (-3 / 2))) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - G p i j) ^ 2)
      ∂(ageμ c (-1 / 2))) atTop (𝓝 0)

/-- **Sub-leaf (completeness of the tensor `L²`)**: a Cauchy sequence of measurable tensor fields in
`L²(ageμ c (-1/2))` has a measurable `L²` limit. -/
def EnergyGradLimit : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ Gk : ℕ → Chart → Fin 2 → Fin 2 → ℂ,
    (∀ k i j, Measurable fun p => Gk k p i j) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gk l p i j) ^ 2)
        ∂(ageμ c (-1 / 2)) < ENNReal.ofReal ε) →
    ∃ G : Chart → Fin 2 → Fin 2 → ℂ, (∀ i j, Measurable fun p => G p i j) ∧
      Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - G p i j) ^ 2)
        ∂(ageμ c (-1 / 2))) atTop (𝓝 0)

/-- **Sub-leaf (velocity limit, bridge `𝓗`-norm ↔ `L²(ageμ c (-3/2))`)**: if `g_k → g` in `𝓗`, and
`b_k = velF (R₀(μ) g_k)` a.e. is measurable, then `b_k → b` in `L²(ageμ c (-3/2))` for a measurable
representative `b = velF (R₀(μ) g)` a.e., which has finite global `L²(ageμ c (-3/2))` energy
(`‖s^{-3/4}·‖` is the `𝓗` norm up to the cell normalisation; `‖R₀(μ)g_k - R₀(μ)g‖ ≤
(Re μ+1/4)⁻¹‖g_k - g‖`, `B0225.norm_R0_le`). -/
def EnergyVelLimit : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ (g : HSpace c MeridC) (gk : ℕ → HSpace c MeridC), Tendsto gk atTop (𝓝 g) →
      ∀ bk : ℕ → Chart → Fin 2 → ℂ,
        (∀ k, bk k =ᵐ[ageμ c (-3 / 2)]
          velF c (UnforcedLeray.B0225.R0 hc ν μ (gk k) : HSpace c MeridC)) →
        (∀ k i, Measurable fun p => bk k p i) →
        ∃ b : Chart → Fin 2 → ℂ, (∀ i, Measurable fun p => b p i) ∧
          b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) ∧
          Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (vnorm2 (fun i => bk k p i - b p i) ^ 2)
            ∂(ageμ c (-3 / 2))) atTop (𝓝 0) ∧
          ∫⁻ p, ENNReal.ofReal (vnorm2 (fun i => b p i) ^ 2) ∂(ageμ c (-3 / 2)) < ⊤

/-- **Sub-leaf (`energyLoc` of the limit)**: on `[s₁,s₂] × cell` the weights are bounded above and
below, so `|b|² + |G|² ≤ 2(|b_k - b|² + |G_k - G|²) + 2(|b_k|² + |G_k|²)` for one `k` with small
error gives local finiteness (`b`, `G` measurable, so the `lintegral` is subadditive). -/
def EnergyLimitLoc : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (bk : ℕ → Chart → Fin 2 → ℂ) (Gk : ℕ → Chart → Fin 2 → Fin 2 → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
    (∀ k, IsEnergyFieldAE c (bk k) (Gk k)) → EnergyL2Limit c bk Gk b G →
      (∀ i, Measurable fun p => b p i) → (∀ i j, Measurable fun p => G p i j) →
      ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤

/-- **Sub-leaf (`divFreeAE` of the limit)**: Fubini gives a subsequence along which the slices
`b_{φ k}(s,·) → b(s,·)` in `L²(cell)` for a.e. `s`; the tested divergence identity (bounded test
`ψ` with bounded derivatives, cell of finite measure) passes to the limit. -/
def EnergyLimitDivFree : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (bk : ℕ → Chart → Fin 2 → ℂ) (Gk : ℕ → Chart → Fin 2 → Fin 2 → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
    (∀ k, IsEnergyFieldAE c (bk k) (Gk k)) → EnergyL2Limit c bk Gk b G →
      (∀ i, Measurable fun p => b p i) →
      ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ ψ, B0579.IsCylTest c ψ →
        ∫ x in B0579.cell c,
          (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0

/-- **Sub-leaf (`weakGradAE` of the limit)**: same subsequence; `HasWeakCellDerivC` (integration
by parts against cell tests) passes to `L²(cell)` limits of `b_k(s,·)` and `G_k(s,·)`. -/
def EnergyLimitWeakGrad : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (bk : ℕ → Chart → Fin 2 → ℂ) (Gk : ℕ → Chart → Fin 2 → Fin 2 → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
    (∀ k, IsEnergyFieldAE c (bk k) (Gk k)) → EnergyL2Limit c bk Gk b G →
      (∀ i, Measurable fun p => b p i) → (∀ i j, Measurable fun p => G p i j) →
      ∀ᵐ s ∂(volume : Measure ℝ), 0 < s → ∀ i j,
        HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)

theorem energyClosure_of (h1 : EnergyGradLimit) (h2 : EnergyVelLimit) (h3 : EnergyLimitLoc)
    (h4 : EnergyLimitDivFree) (h5 : EnergyLimitWeakGrad) : EnergyClosure := by
  intro c ν hc hν μ hμ g gk hg bk Gk hk hcauchy
  obtain ⟨G, hGm, hGlim⟩ := h1 c hc Gk (fun k => (hk k).2.gradMeasurable) hcauchy
  obtain ⟨b, hbm, hbae, hblim, hbfin⟩ :=
    h2 c ν hc hν μ hμ g gk hg bk (fun k => (hk k).1) (fun k => (hk k).2.measurable)
  have hE : ∀ k, IsEnergyFieldAE c (bk k) (Gk k) := fun k => (hk k).2
  have hL : EnergyL2Limit c bk Gk b G := ⟨hblim, hGlim⟩
  refine ⟨b, G, hbae, ?_⟩
  refine ⟨hbm, hGm, h3 c hc bk Gk b G hE hL hbm hGm, ⟨1, one_pos, ?_⟩, h4 c hc bk Gk b G hE hL hbm,
    h5 c hc bk Gk b G hE hL hbm hGm⟩
  exact lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hbfin

end UnforcedLeray.Short.PartIIa.N01
