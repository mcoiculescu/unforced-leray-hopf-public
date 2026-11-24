import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2

/-!
# `MollCommutatorLimit`: decomposition

Source `the November 2 reference manuscript` lines 1351-1362 and 1556-1583.
(i) the adjoint equation of `FWUAdjDom` (stated against solenoidal tests) extends to all phase
tests; (ii) with the full equation, `ρ ⋆` commutes with `∂_τ`, `Δ`, and the drift commutator is a
Friedrichs commutator on the compact `y`-support, tending to `0` in `Y_2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- **Full-equation extension** (source 1351-1362, 1556-1583): for `Φ` in the adjoint graph
domain with `(μ + L₀ᵗ)Φ = g`, the equation holds against every phase test, not only solenoidal
ones.  `h = (μ + L₀ᵗ)Φ - g ∈ Y_2` (FWUAdjDom.lapl/drift) is weakly solenoidal (`𝒯ᵗ` and `Δ`
preserve divergence: `div(y·∇u) = div u + y·∇ div u`; `g` solenoidal) and orthogonal to all
solenoidal tests, hence zero (Helmholtz decomposition of phase tests; the projected curl
cutoffs `Cons.C03.Concrete.isSolTest_projectedPotentialCurlCutoff`). -/
def AdjFullEquation : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g →
      ∀ Ψ, IsPhaseTest P Ψ →
        pairF P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) Φ = pairF P Ψ g

/-- **Friedrichs limit under the full equation** (source 1556-1583): if the adjoint equation holds
against all phase tests then `(μ + L₀ᵗ)(ρ ⋆ Φ) - ρ ⋆ g → 0` in `Y_2` as the radius of `ρ` tends
to `0` (`ρ ⋆` commutes with `∂_τ`, `Δ`; `(μ + L₀ᵗ)(ρ⋆Φ) - ρ⋆((μ + L₀ᵗ)Φ) = ½[y·∇, ρ⋆]Φ`, a
Friedrichs commutator on the compact `y`-support, bounded by `‖Φ‖_{Y_2}`, tending to `0` on the
dense class and hence on `Y_2`). -/
def MollCommutatorLimitFull : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ →
      (∀ Ψ, IsPhaseTest P Ψ →
        pairF P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) Φ = pairF P Ψ g) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ContDiffBump (0 : ℝ × Space), ρ.rOut < δ → ρ.rOut = 2 * ρ.rIn →
        UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - mollP ρ g x) <
            ENNReal.ofReal ε

theorem mollCommutatorLimit_of (h1 : AdjFullEquation) (h2 : MollCommutatorLimitFull) :
    MollCommutatorLimit := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ hs ε hε
  exact h2 P ν μ hP hP1 hν hμ Φ g hΦ hs (h1 P ν μ hP hP1 hν hμ Φ g hΦ) ε hε

end UnforcedLeray.Short.PartIIIb.Concrete
