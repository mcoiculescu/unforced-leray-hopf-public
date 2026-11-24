import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# `streamPotIntertwine`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
With `F(Θ) := ⟪(L₀+μ-½)Θ, ψ⟫ - ⟪Θ, w⟫` (a tempered distribution on phase tests), the difference
`wOpT^t ψ - w` is curl-free (the equation of `FWUAdjDom` tested on `curl Θ`, using the
commutation `curl (y·∇ψ) = y·∇ curl ψ + curl ψ`), divergence-free (both `ψ, w` are weakly
solenoidal and `div` commutes with `wOpT`), hence a tempered harmonic field, which vanishes (Fourier
side: the degree `-1` multiplier `iξ×/|ξ|²` commutes with `∂_τ`, `|ξ|²`, `ξ·∇_ξ` up to the
`3/2 → 1/2` shift; no atom at `ξ = 0` because `ψ̂ ∈ |ξ|⁻¹ L²_loc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The defect functional `Θ ↦ ⟪wOpT Θ, ψ⟫ - ⟪Θ, w⟫`. -/
def IntertwineDefect (P ν μ : ℝ) (ψ w : ℝ × Space → CVec3) (Θ : ℝ × Space → CVec3) : ℂ :=
  pairF P (wOpT ν μ Θ) ψ - pairF P Θ w

/-- (a) The defect vanishes on curls of phase tests (source 1351-1362): by `dom.equation` on the
solenoidal tests `curl Θ`, `curlT (wOpT Θ) = (L₀ + μ) curlT Θ` and `StreamPot.curl` for `ψ, w`. -/
def IntertwineCurl : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g ψ w : ℝ × Space → CVec3) (Dψ Dw : Fin 3 → ℝ × Space → CVec3),
      FWUAdjDom P ν μ Φ g → StreamPot P Φ ψ Dψ → StreamPot P g w Dw →
        ∀ Θ, IsPhaseTest P Θ → IntertwineDefect P ν μ ψ w (curlT Θ) = 0

/-- (b) The defect vanishes on gradients of scalar phase tests (`div ψ = div w = 0` weakly, and
`wOpT (∇φ) = ∇ (L₀ + μ + 1/2 - ... ) φ` is again a gradient of a phase test: `∇` commutes with
`wOpT` up to the constant shift). -/
def IntertwineGrad : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g ψ w : ℝ × Space → CVec3) (Dψ Dw : Fin 3 → ℝ × Space → CVec3),
      FWUAdjDom P ν μ Φ g → StreamPot P Φ ψ Dψ → StreamPot P g w Dw →
        ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → IntertwineDefect P ν μ ψ w (gradT φ) = 0

/-- (c) Liouville / Fourier vanishing (source 1351-1362): a defect that vanishes on all curls and
all gradients of phase tests vanishes (tempered harmonic field with `|ξ|⁻¹ L²_loc` profile). -/
def IntertwineLiouville : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g ψ w : ℝ × Space → CVec3) (Dψ Dw : Fin 3 → ℝ × Space → CVec3),
      FWUAdjDom P ν μ Φ g → StreamPot P Φ ψ Dψ → StreamPot P g w Dw →
        (∀ Θ, IsPhaseTest P Θ → IntertwineDefect P ν μ ψ w (curlT Θ) = 0) →
        (∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → IntertwineDefect P ν μ ψ w (gradT φ) = 0) →
        ∀ Θ, IsPhaseTest P Θ → IntertwineDefect P ν μ ψ w Θ = 0

theorem streamPotIntertwine_of (h1 : IntertwineCurl) (h2 : IntertwineGrad)
    (h3 : IntertwineLiouville) : StreamPotIntertwine := by
  intro P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw Θ hΘ
  have := h3 P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw
    (h1 P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw)
    (h2 P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw) Θ hΘ
  exact sub_eq_zero.mp this

end UnforcedLeray.Short.PartIIIb.Concrete
