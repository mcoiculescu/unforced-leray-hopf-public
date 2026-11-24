import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1

/-!
# Part III-a, `PartIII-a:T18/3/1/4`: `CoreImpliesWeighted` in three lemmas

Source of record: `the November 2 reference manuscript`, lines 3541-3552 (weighted
identity for `u = g^{-1} b`) and 3427-3440.

* `EnergyLocIntegrable` (Lemma 1): for the standing data, `E`, `N`, `R` and
  `J(s) = ∫_cell |F||G|` are integrable in `s` on every `[s₁, s₂] ⊂ (0,∞)`.
  Route: `energyLoc`, `L2locTensor`, Tonelli (`lintegral_prod`, `StronglyMeasurable.integral_prod_right`)
  and Cauchy-Schwarz for the product term.
* Lemma 2 (`CoreToSmoothWeighted`): `CoreIdentity` with the weight `w = ψ s^{-1/2} g^{-2}` gives the
  weighted inequality for smooth `ψ` (algebra with `gainG`, drop the term `2 h ψ s^{-1/2} E_u ≥ 0`,
  use `-R_u ≤ ∫_cell |F̃||G̃|` a.e. in `s`).
* Lemma 3 (`SmoothToC1Weighted`): pass from smooth to `C¹` weights `ψ` by convolution with a
  nonnegative `ContDiffBump.normed` kernel and dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Lemma 1** (SP 3541-3552; local integrability in `s` of the cell energies).  For the standing
data, on every `[s₁, s₂] ⊂ (0,∞)` the functions `E`, `N`, `R` and `J(s) = ∫_cell |F(s,x)||G(s,x)|`
are integrable in `s`. -/
def EnergyLocIntegrable : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), FreeSolData c ν μ F b G →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      IntegrableOn (energyE c b) (Icc s₁ s₂) ∧ IntegrableOn (energyN c G) (Icc s₁ s₂) ∧
      IntegrableOn (energyR c F G) (Icc s₁ s₂) ∧
      IntegrableOn (fun s => ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)))
        (Icc s₁ s₂)

/-- The weighted energy inequality for **smooth** weights `ψ` (same statement as
`WeightedEnergyIdentity` with `ContDiff ℝ ∞ ψ` in place of `ContDiff ℝ 1 ψ`). -/
def WeightedEnergyIdentitySmooth : Prop :=
  ∀ (c ν γ : ℝ) (μ : ℂ), 0 < c → 0 < ν → 0 ≤ γ →
    ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤) →
    (∀ i j, Measurable fun p => F p i j) →
    IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 → (∀ s, 0 ≤ ψ s) →
      (∫ s in Ioi (0 : ℝ), ψ s *
          ((1 / 2 + 2 * μ.re) * s ^ (-3 / 2 : ℝ) *
              (∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2) +
            2 * ν * s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2))
        ≤ (∫ s in Ioi (0 : ℝ), deriv ψ s *
            (s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2)) +
          2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) *
            ∫ x in B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) * tnorm2 (gainConj γ ν G (s, x))

/-- **Lemma 2** (SP 3541-3552): `CoreIdentity` for all standing data, and the local integrability
of Lemma 1, give the weighted inequality for smooth cutoffs.  Take `w s = ψ s * s^(-1/2) *
(gainG γ ν s)^(-2)` in `CoreIdentity` (smooth, compact support in `(0,∞)`); the algebra is
`deriv w = g^{-2}(ψ' s^{-1/2} - ½ ψ s^{-3/2} - 2 h ψ s^{-1/2})`, `h = γ/(1+νs)²`, and
`vnorm2 (gainConj γ ν b) = g⁻¹ vnorm2 b` (see `Sub/Audit0/AuditT18_3_1_4_GainFactsCorrected.lean`). -/
def CoreToSmoothWeighted : Prop :=
  CoreAll → EnergyLocIntegrable → WeightedEnergyIdentitySmooth

/-- **Lemma 3** (SP 3541-3552): from smooth to `C¹` cutoffs.  `ψₖ = ψ ⋆ ρ_{1/k}` with a nonnegative
`ContDiffBump.normed` kernel: smooth, `≥ 0`, supports in a fixed compact subset of `(0,∞)`,
`ψₖ → ψ` and `ψₖ' → ψ'` uniformly; both sides are integrals over that compact set of the `L¹`
functions `E_u`, `N_u`, `J̃` (Lemma 1 and the gain scaling) against bounded functions, so the
inequality passes to the limit (`le_of_tendsto_of_tendsto'`,
`tendsto_integral_of_dominated_convergence`). -/
def SmoothToC1Weighted : Prop :=
  EnergyLocIntegrable → WeightedEnergyIdentitySmooth → WeightedEnergyIdentity

/-- `CoreImpliesWeighted` from the three lemmas. -/
theorem coreImpliesWeighted_of (h1 : EnergyLocIntegrable) (h2 : CoreToSmoothWeighted)
    (h3 : SmoothToC1Weighted) : CoreImpliesWeighted :=
  fun hCore => h3 h1 (h2 hCore h1)

end UnforcedLeray.Short.IIIa
