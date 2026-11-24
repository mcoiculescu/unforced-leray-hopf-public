import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4

/-!
# `AdjFullEquation`: decomposition

Source `the November 2 reference manuscript` lines 1351-1362 and 1556-1583.
(1) integration by parts: `⟪(μ + L₀)Ψ, Φ⟫ - ⟪Ψ, g⟫ = ⟪Ψ, h⟫` for a weakly solenoidal `h ∈ Y_2`;
(2) Helmholtz orthogonality: a weakly solenoidal `h ∈ Y_2` orthogonal to all solenoidal phase tests
is orthogonal to all phase tests (solenoidal tests are dense in the weakly solenoidal part of `Y_2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- **Integration by parts for the adjoint graph domain** (source 1351-1362, 1556-1583): for
`Φ ∈ FWUAdjDom` with `(μ + L₀ᵗ)Φ = g` there is a weakly solenoidal `h ∈ Y_2`
(`h = (μ + L₀ᵗ)Φ - g` with `νΔΦ`, `𝒯Φ` the `Y_2` fields of `FWUAdjDom.lapl/drift`; weak
solenoidality because `Δ` and `𝒯ᵗ` preserve divergence, `div(y·∇u) = div u + y·∇ div u`, and `Φ`,
`g` are weakly solenoidal) such that for every phase test `Ψ`
`⟪(μ + L₀)Ψ, Φ⟫ - ⟪Ψ, g⟫ = ⟪Ψ, h⟫`. -/
def AdjIntParts : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g →
      ∃ h : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 h ∧ IsWeakSolenoidal P h ∧
        ∀ Ψ, IsPhaseTest P Ψ →
          pairF P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) Φ - pairF P Ψ g = pairF P Ψ h

/-- **Helmholtz orthogonality** (source 1351-1362): a weakly solenoidal `h ∈ Y_2` with
`⟪Ψ, h⟫ = 0` for every solenoidal phase test `Ψ` has `⟪Ψ, h⟫ = 0` for every phase test `Ψ`.
(Solenoidal compactly supported tests, e.g. the projected curl cutoffs of
`Cons.C03.Concrete.isSolTest_projectedPotentialCurlCutoff`, are dense in the weakly solenoidal
part of `Y_2`, so `h = 0`; alternatively the gradient part of a general test pairs to zero.) -/
def HelmholtzOrth : Prop :=
  ∀ (P : ℝ), 0 < P → P ≤ 1 → ∀ h : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 h → IsWeakSolenoidal P h →
      (∀ Ψ, IsSolTest P Ψ → pairF P Ψ h = 0) →
        ∀ Ψ, IsPhaseTest P Ψ → pairF P Ψ h = 0

theorem adjFullEquation_of (h1 : AdjIntParts) (h2 : HelmholtzOrth) : AdjFullEquation := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ Ψ hΨ
  obtain ⟨h, hmem, hsol, hid⟩ := h1 P ν μ hP hP1 hν hμ Φ g hΦ
  have h0 : ∀ Ψ, IsSolTest P Ψ → pairF P Ψ h = 0 := by
    intro Ψ' hΨ'
    rw [← hid Ψ' hΨ'.1, hΦ.equation Ψ' hΨ', sub_self]
  have := h2 P hP hP1 h hmem hsol h0 Ψ hΨ
  have e := hid Ψ hΨ
  rw [this] at e
  exact sub_eq_zero.1 e

end UnforcedLeray.Short.PartIIIb.Concrete
