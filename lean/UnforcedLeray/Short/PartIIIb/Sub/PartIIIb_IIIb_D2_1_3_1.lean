import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_3

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- `Φ` lies in the adjoint graph domain at `r = 2` with `(μ + L₀ᵗ)Φ = g` in the weak sense
(source 1351-1362, `bg:common-body-graph` at `r = 2`: the adjoint has the same maximal graph):
`Φ, νΔΦ, 𝒯Φ ∈ Y_2` (as distributions, via `HasPtwOp`), `Φ` and `g` weakly solenoidal, and
`⟪(μ + L₀)Ψ, Φ⟫ = ⟪Ψ, g⟫` for every solenoidal phase test `Ψ` (`L₀` the transpose of `L₀ᵗ`). -/
structure FWUAdjDom (P ν μ : ℝ) (Φ g : ℝ × Space → CVec3) : Prop where
  mem : UnforcedLeray.Short.IIb.IsInYr P 2 Φ
  mem_g : UnforcedLeray.Short.IIb.IsInYr P 2 g
  sol : IsWeakSolenoidal P Φ
  sol_g : IsWeakSolenoidal P g
  lapl : ∃ a, UnforcedLeray.Short.IIb.IsInYr P 2 a ∧
    UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a
  drift : ∃ b, UnforcedLeray.Short.IIb.IsInYr P 2 b ∧
    UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b
  equation : ∀ Ψ, IsSolTest P Ψ →
    pairF P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) Φ = pairF P Ψ g

/-- **Adjoint solvability** (source 1351-1362, `bg:common-body-graph` at `r = 2`, Leray projection
of the datum 1361): for `0 < P ≤ 1`, `ν > 0`, `μ + 1/4 > 0`, every weakly solenoidal `f ∈ Y_2` is
`(μ + L₀ᵗ)Φ` for some `Φ` in the adjoint graph domain (the adjoint of the `r = 2` bijection of
`PartIIa.commonBodyBijective_of_parts`). -/
def FWUAdjSolve : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ f : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 f → IsWeakSolenoidal P f →
      ∃ Φ, FWUAdjDom P ν μ Φ f

/-- **Solenoidal density in the adjoint graph norm** (source 1361 and the stream-potential
cutoff `curl(χₙ ψ)`, plus mollification in `y`): if `Φ` is in the adjoint graph domain with
`(μ + L₀ᵗ)Φ = g` then there are solenoidal phase tests `Φₙ` with `(μ + L₀ᵗ)Φₙ ∈ Y_2` converging
to `g` in `Y_2`. -/
def FWUAdjDensity : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g →
      ∃ Φn : ℕ → ℝ × Space → CVec3, (∀ n, IsSolTest P (Φn n)) ∧
        (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => L0T ν (Φn n) x + (μ : ℂ) • Φn n x)) ∧
        Tendsto (fun n => UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => L0T ν (Φn n) x + (μ : ℂ) • Φn n x - g x)) atTop (𝓝 0)

theorem fwuDense_of (h1 : FWUAdjSolve) (h2 : FWUAdjDensity) : FWUDense := by
  intro P ν μ hP hP1 hν hμ f hf hs
  obtain ⟨Φ, hΦ⟩ := h1 P ν μ hP hP1 hν hμ f hf hs
  exact h2 P ν μ hP hP1 hν hμ Φ f hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
