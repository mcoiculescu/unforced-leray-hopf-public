import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3
import UnforcedLeray.Short.PartIIb.Bridge.Adjoint

/-!
# `intertwineCurl`: decomposition

Source `the November 2 reference manuscript`
lines 1351-1362 (adjoint at `r = 2` has the maximal graph, `Φ ∈ D(L₀ᵗ)`, equation tested on
solenoidal tests) and 1470-1480.

Mathematics.  For a phase test `Θ`, `curlT Θ` is a solenoidal phase test and
`wOpT (curlT Θ) = curlT ((L₀ + μ) Θ)` (curl commutes with `∂_τ`, `Δ`, and
`curl (y·∇Θ) = y·∇ curl Θ + curl Θ`).  With `curl ψ = Φ`, `curl w = g`:
`defect (curl Θ) = ⟪(L₀+μ)Θ, Φ⟫ - ⟪Θ, g⟫`.  The right side vanishes for solenoidal `Θ` by
`FWUAdjDom.equation`; for all phase tests it vanishes because the remainder field
`h = (1+μ)Φ - a - b - g ∈ Y_2` (`a = νΔΦ`, `b = 𝒯Φ`, both in `Y_2` since `Φ ∈ D_2`, source
line 1349) is weakly solenoidal and annihilates
solenoidal tests (Leray density in `L²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The remainder field `h = (1+μ)Φ - a - b - g` (`a = νΔΦ`, `b = 𝒯Φ` weakly). -/
def remH (μ : ℝ) (Φ g a b : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ((1 + μ : ℝ) : ℂ) • Φ x - a x - b x - g x

/-- Curl commutes with `wOpT` up to the `3/2 → 1/2` shift (source 1351-1362): for smooth `Θ`,
`wOpT ν μ (curl Θ) = curl ((L₀ + μ) Θ)`. -/
def CurlCommute : Prop :=
  ∀ (ν μ : ℝ) (Θ : ℝ × Space → CVec3), ContDiff ℝ ∞ Θ →
    wOpT ν μ (curlT Θ) = curlT (fun x => L0 ν Θ x + (μ : ℂ) • Θ x)

/-- The pairing formula for the remainder field: with `a = νΔΦ`, `b = 𝒯Φ` weakly and
`a, b ∈ Y_2`, for every phase test `Θ`, `⟪(L₀+μ)Θ, Φ⟫ - ⟪Θ, g⟫ = ⟪Θ, h⟫` (transposing `𝒯`, `νΔ`
onto `Φ`; `L₀ = 𝒯 - νΔ - ½`, `𝒯 = -driftT + 3/2`).  The memberships `a, b ∈ Y_2` are part of the
adjoint graph domain (source
`the November 2 reference manuscript` 1349:
`D_2 = {w ∈ Y_2 : νΔw, 𝒯w ∈ Y_2}`; 1365: at `r = 2` the adjoint has the same maximal graph;
1470-1473: the actual adjoint domain is `D_2`); they make `⟪Θ, a⟫`, `⟪Θ, b⟫` integrable pairings,
which the second-slot split `⟪Θ, (1+μ)Φ - a - b - g⟫ = …` needs. -/
def AdjRemainderFormula : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g a b : ℝ × Space → CVec3), FWUAdjDom P ν μ Φ g →
      UnforcedLeray.Short.IIb.IsInYr P 2 a → UnforcedLeray.Short.IIb.IsInYr P 2 b →
      UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a →
      UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b →
      ∀ Θ, IsPhaseTest P Θ →
        pairF P (fun x => L0 ν Θ x + (μ : ℂ) • Θ x) Φ - pairF P Θ g
          = pairF P Θ (remH μ Φ g a b)

/-- `h = remH ∈ Y_2` (linear combination of `Φ, g, a, b ∈ Y_2`). -/
def AdjRemainderMem : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g a b : ℝ × Space → CVec3), FWUAdjDom P ν μ Φ g →
      UnforcedLeray.Short.IIb.IsInYr P 2 a → UnforcedLeray.Short.IIb.IsInYr P 2 b →
      UnforcedLeray.Short.IIb.IsInYr P 2 (remH μ Φ g a b)

/-- `h = remH` is weakly solenoidal: `Φ, g` are, and `⟪∇φ, a⟫ = ⟪νΔ∇φ, Φ⟫ = 0`,
`⟪∇φ, b⟫ = ⟪driftT ∇φ, Φ⟫ = 0` since `Δ`, `∂_τ`, `y·∇` map gradients to gradients
(`gr_dτ`, `gr_lap`, `gr_radial` of `GradAux`).  As in `AdjRemainderFormula`, `a, b ∈ Y_2` are
part of the adjoint graph domain (source
`the November 2 reference manuscript` 1349, 1365,
1470-1473) and are needed to split `⟪∇φ, (1+μ)Φ - a - b - g⟫` in its second slot. -/
def AdjRemainderSol : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ (Φ g a b : ℝ × Space → CVec3), FWUAdjDom P ν μ Φ g →
      UnforcedLeray.Short.IIb.IsInYr P 2 a → UnforcedLeray.Short.IIb.IsInYr P 2 b →
      UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) Φ a →
      UnforcedLeray.Short.IIb.HasPtwOp P driftT Φ b →
      IsWeakSolenoidal P (remH μ Φ g a b)

/-- **Leray density in `L²`** (source 1351-1362): a weakly solenoidal `h ∈ Y_2` annihilating all
solenoidal phase tests annihilates all phase tests (`h` is then a gradient and weakly
divergence-free, so `Δh = 0` weakly and `h ∈ L²` harmonic vanishes). -/
def LerayDensityL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ h : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 h → IsWeakSolenoidal P h →
      (∀ Ψ, IsSolTest P Ψ → pairF P Ψ h = 0) → ∀ Θ, IsPhaseTest P Θ → pairF P Θ h = 0

/-- The equation of `FWUAdjDom`, extended from solenoidal tests to all phase tests. -/
theorem adjEquation_all (h2 : AdjRemainderFormula) (h3 : AdjRemainderMem) (h4 : AdjRemainderSol)
    (h5 : LerayDensityL2) :
    ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
      ∀ (Φ g : ℝ × Space → CVec3), FWUAdjDom P ν μ Φ g →
        ∀ Θ, IsPhaseTest P Θ →
          pairF P (fun x => L0 ν Θ x + (μ : ℂ) • Θ x) Φ = pairF P Θ g := by
  intro P ν μ hP hP1 hν hμ Φ g hdom Θ hΘ
  obtain ⟨a, ha, hla⟩ := hdom.lapl
  obtain ⟨b, hb, hdb⟩ := hdom.drift
  have hmem := h3 P ν μ hP hP1 hν hμ Φ g a b hdom ha hb
  have hsol := h4 P ν μ hP hP1 hν hμ Φ g a b hdom ha hb hla hdb
  have hann : ∀ Ψ, IsSolTest P Ψ → pairF P Ψ (remH μ Φ g a b) = 0 := by
    intro Ψ hΨ
    rw [← h2 P ν μ hP hP1 hν hμ Φ g a b hdom ha hb hla hdb Ψ hΨ.1, hdom.equation Ψ hΨ]
    simp
  have := h5 P hP _ hmem hsol hann Θ hΘ
  have h6 := h2 P ν μ hP hP1 hν hμ Φ g a b hdom ha hb hla hdb Θ hΘ
  rw [this] at h6
  exact sub_eq_zero.mp h6

theorem intertwineCurl_of (h1 : CurlCommute) (h2 : AdjRemainderFormula) (h3 : AdjRemainderMem)
    (h4 : AdjRemainderSol) (h5 : LerayDensityL2) : IntertwineCurl := by
  intro P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw Θ hΘ
  have hX : IsPhaseTest P (fun x => L0 ν Θ x + (μ : ℂ) • Θ x) :=
    (UnforcedLeray.Short.IIb.isPhaseTest_L0 hΘ ν).add (hΘ.const_smul (μ : ℂ))
  unfold IntertwineDefect
  rw [h1 ν μ Θ hΘ.smooth, hψ.curl _ hX, hw.curl Θ hΘ,
    adjEquation_all h2 h3 h4 h5 P ν μ hP hP1 hν hμ Φ g hdom Θ hΘ]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
