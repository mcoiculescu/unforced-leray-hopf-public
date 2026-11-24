import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalNormalizedScalarDyson

/-!
# The normalized Gaussian free family is the scalar Dyson perturbation of the diffusion clock

The scalar gauge is identified with the actual bounded Dyson interaction on each finite
turnover block, by the concrete scalar FTC and Dyson uniqueness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.Evolution

/-- The concrete clamped diffusion evolution on an active turnover block. -/
def turnoverBlockDiffusionFamily (R b₀ : ℝ) (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    EvolutionFamily XG 0 (R - b₀) :=
  freeDiffusionFamily (turnoverBlockBeta R b₀)
    (fun s t => intervalIntegrable_turnoverBlockBeta hb₀ hR)
    (fun τ => le_of_lt (turnoverBlockBeta_pos hb₀ hR)) (1 / b₀)
    (fun τ => by
      have hp := turnoverBlockBeta_pos hb₀ hR (t := τ)
      have hu := turnoverBlockBeta_le_inv hb₀ hR (t := τ)
      rw [abs_of_pos hp]
      exact hu)

/-- The actual bounded scalar gauge perturbation on the same block. -/
def turnoverBlockScalarPerturbation (lam κ : ℂ) (R b₀ : ℝ)
    (hb₀ : 0 < b₀) (hR : b₀ ≤ R) : BoundedPert XG 0 (R - b₀) :=
  turnoverScalarPert lam κ R b₀ hb₀ hR 0 (R - b₀)

/-- On a finite turnover block, the actual gauge-conjugated Gaussian family is the Dyson
perturbation of the clamped diffusion clock by the bounded scalar coefficient `-lam - beta*kappa`.
The equality is proved from its mild equation, whose scalar integral is the FTC proved in
`turnoverScalarGauge_integral`. -/
theorem normalizedTurnoverFree_eq_scalar_dyson
    {lam κ : ℂ} {R b₀ : ℝ} (hb₀ : 0 < b₀) (hR : b₀ ≤ R) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ R - b₀ →
      normalizedTurnoverFree lam κ R t s =
        (dyson (turnoverBlockDiffusionFamily R b₀ hb₀ hR)
          (turnoverBlockScalarPerturbation lam κ R b₀ hb₀ hR)).U t s := by
  let β : ℝ → ℝ := turnoverBlockBeta R b₀
  let E : EvolutionFamily XG 0 (R - b₀) :=
    turnoverBlockDiffusionFamily R b₀ hb₀ hR
  let S : BoundedPert XG 0 (R - b₀) :=
    turnoverBlockScalarPerturbation lam κ R b₀ hb₀ hR
  let N : EvolutionFamily XG 0 (R - b₀) :=
    normalizedTurnoverFreeFamily lam κ R b₀ hb₀ hR
  have hcont : ∀ s, 0 ≤ s → s ≤ R - b₀ → ∀ x : XG,
      ContinuousOn (fun t => N.U t s x) (Icc s (R - b₀)) := by
    intro s hs hsb x
    have hline : ContinuousOn (fun t : ℝ => (s, t)) (Icc s (R - b₀)) :=
      continuousOn_const.prodMk continuousOn_id
    have hmap : MapsTo (fun t : ℝ => (s, t)) (Icc s (R - b₀))
        {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀} := by
      intro t ht
      exact ⟨hs, ht.1, ht.2⟩
    have hjoint : ContinuousOn
        (fun p : ℝ × ℝ => N.U p.2 p.1 x)
        {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R - b₀} := N.U_cont x
    have hcomp := hjoint.comp hline hmap
    change ContinuousOn (fun t : ℝ => N.U t s x) (Icc s (R - b₀)) at hcomp
    exact hcomp
  have heq : ∀ s t, 0 ≤ s → s ≤ t → t ≤ R - b₀ → ∀ x : XG,
      N.U t s x = E.U t s x + ∫ r in s..t, E.U t r (S.A r (N.U r s x)) := by
    intro s t hs hst ht x
    let γ : ℝ → ℂ := fun r => gauge lam κ (R - r) * gaugeInv lam κ (R - s)
    let c : ℝ → ℂ := fun r => -lam - ((β r : ℝ) : ℂ) * κ
    have hV : ∀ u, s ≤ u → u ≤ R - b₀ →
        N.U u s x = γ u • E.U u s x := by
      intro u hsu hu
      have hfree := normalizedTurnoverFree_eq_scalar_clampedDiffusion
        (lam := lam) (κ := κ) (R := R) (b₀ := b₀) hb₀ hR hs hsu hu
      have hratio := gaugeRatio_eq_scalarExp_turnover
        (lam := lam) (κ := κ) (R := R) (b₀ := b₀) hb₀ hs hsu hu
      change normalizedTurnoverFree lam κ R u s x = _
      rw [hfree, ← hratio]
      rfl
    have hscalar := turnoverScalarGauge_integral
      (lam := lam) (κ := κ) (R := R) (b₀ := b₀) (s := s) (t := t)
      hb₀ hR hs hst ht
    have hintegrand : ∀ r ∈ uIcc s t,
        E.U t r (S.A r (N.U r s x)) = (c r * γ r) • E.U t s x := by
      intro r hr
      rw [uIcc_of_le hst] at hr
      have hsr : s ≤ r := hr.1
      have hrt : r ≤ t := hr.2
      have hVr := hV r hsr (hrt.trans ht)
      have hcomp := congrArg (fun L : XG →L[ℂ] XG => L x)
        (E.U_comp hs hsr hrt ht)
      change E.U t r (E.U r s x) = E.U t s x at hcomp
      change E.U t r
        ((-lam - ((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG) (N.U r s x)) = _
      rw [hVr]
      simp only [map_smul, one_apply_eq_self, smul_smul]
      rw [hcomp]
    rw [show N.U t s x = γ t • E.U t s x from hV t hst ht]
    rw [intervalIntegral.integral_congr (fun r hr => hintegrand r hr)]
    rw [intervalIntegral.integral_smul_const]
    rw [hscalar]
    simp only [sub_smul, one_smul]
    module
  have hN := Evolution.dyson_unique (F := E) (A := S) (V := N.U) hcont heq
  intro s t hs hst ht
  have hresult := hN s t hs hst ht
  change normalizedTurnoverFree lam κ R t s =
    (dyson (turnoverBlockDiffusionFamily R b₀ hb₀ hR)
      (turnoverBlockScalarPerturbation lam κ R b₀ hb₀ hR)).U t s at hresult
  exact hresult

end UnforcedLeray.Cons.G3b
