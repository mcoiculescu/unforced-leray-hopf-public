import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `adjDomGrad`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`Φ, νΔΦ ∈ Y_2` give, for a.e. phase `τ`, `Φ(τ) ∈ H²(ℝ³)` and `‖∇Φ(τ)‖² ≤ ‖Φ(τ)‖ ‖ΔΦ(τ)‖`
(Fourier); the weak derivative is measurable in `τ`, periodic and in `Y_2`; integration by parts
in `y` per phase, then Fubini, gives `HasPtwOp`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- (a) Per-phase `H¹` regularity (source 1351-1362): for `Φ ∈ FWUAdjDom` there are jointly
measurable periodic `DΦ j ∈ Y_2` such that for a.e. phase `τ` and every smooth compactly supported
`θ : Space → CVec3`, `-∫ ∑ᵢ Φ(τ,y)ᵢ ∂ⱼθᵢ(y) dy = ∫ ∑ᵢ DΦ j (τ,y)ᵢ θᵢ(y) dy`. -/
def AdjDomGradSlice : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g →
      ∃ DΦ : Fin 3 → ℝ × Space → CVec3, ∀ j : Fin 3,
        UnforcedLeray.Short.IIb.IsInYr P 2 (DΦ j) ∧
          ∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
            -(∫ y : Space, ∑ i : Fin 3,
                Φ (τ, y) i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
              = ∫ y : Space, ∑ i : Fin 3, DΦ j (τ, y) i * θ y i

/-- (b) Fubini assembly (source 1351-1362): a slice-wise weak derivative of a `Y_2` field with a
`Y_2` candidate is a weak derivative against phase tests (`HasPtwOp`). -/
def AdjDomGradFubini : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ D : ℝ × Space → CVec3) (j : Fin 3),
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 D →
      (∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        -(∫ y : Space, ∑ i : Fin 3,
            Φ (τ, y) i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
          = ∫ y : Space, ∑ i : Fin 3, D (τ, y) i * θ y i) →
      UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy j Θ) Φ D

theorem adjDomGrad_of (h1 : AdjDomGradSlice) (h2 : AdjDomGradFubini) : AdjDomGrad := by
  intro P ν μ hP hP1 hν hμ Φ g hdom
  obtain ⟨D, hD⟩ := h1 P ν μ hP hP1 hν hμ Φ g hdom
  exact ⟨D, fun j => ⟨(hD j).1, h2 P hP Φ (D j) j hdom.mem (hD j).1 (hD j).2⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
