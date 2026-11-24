import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PhaseLpTri2

/-!
# `FWUAdjMoll`: decomposition into four mollification lemmas

Source: `the November 2 reference manuscript` lines 1351-1362
(`bg:common-body-graph` at `r = 2`: the adjoint has the same maximal graph) and 1556-1583
(mollified differences converge strongly; the equation passes to the limit).
Route: mollify `Φ` in `(τ, y)` by `Φ_ρ = ρ ⋆ Φ` (`Φ` is `P`-periodic in `τ`, `y`-compactly
supported, so `Φ_ρ` is a solenoidal phase test), and show `(μ + L₀ᵗ)Φ_ρ → g` in `Y_2`
(`ρ ⋆ g → g`, and the Friedrichs commutator of `ρ ⋆` with the drift `𝒯ᵗ` vanishes in `Y_2`,
while `ρ ⋆` commutes exactly with `Δ` and `∂_τ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The `(τ, y)`-mollification `ρ ⋆ Φ = ∫ ρ_norm(z) Φ(x - z) dz` of a field on `ℝ × ℝ³`
(for `P`-periodic `Φ` the result is again `P`-periodic in `τ`). -/
def mollP (ρ : ContDiffBump (0 : ℝ × Space)) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ z, ρ.normed volume z • Φ (x - z)

/-- **Leaf 1** (smoothing, periodicity, support, solenoidality; source 1351-1362): the
mollification of a `y`-compactly supported element `Φ` of the adjoint graph domain is a
solenoidal phase test (smooth, `P`-periodic, `y`-compact support; `div_y(ρ ⋆ Φ) = ρ ⋆ div_y Φ = 0`
tested against the periodised shifted kernel, as `Φ` is weakly solenoidal). -/
def MollIsSolTestL : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ →
      ∀ ρ : ContDiffBump (0 : ℝ × Space), IsSolTest P (mollP ρ Φ)

/-- **Leaf 2**: `(μ + L₀ᵗ)(ρ ⋆ Φ) ∈ Y_2` (a smooth `P`-periodic `y`-compactly supported field
lies in `Y_2`; `L₀ᵗ` preserves phase tests). -/
def MollGraphInYr : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ →
      ∀ ρ : ContDiffBump (0 : ℝ × Space),
        UnforcedLeray.Short.IIb.IsInYr P 2
          (fun x => L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x)

/-- **Leaf 3** (approximate identity on the cell): for `g ∈ Y_2` the mollification `ρ ⋆ g` is
measurable and `‖ρ ⋆ g - g‖_{Y_2} → 0` as the support radius of `ρ` tends to `0`
(`L²` approximate identity on `ℝ × ℝ³`, applied to the periodic `g` over the cell
`(0, P] × ℝ³`; Minkowski/Young for the normalised kernel). -/
def MollApproxIdentity : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ContDiffBump (0 : ℝ × Space), ρ.rOut < δ →
      AEStronglyMeasurable (mollP ρ g) volume ∧
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => mollP ρ g x - g x) < ENNReal.ofReal ε

/-- **Leaf 4** (Friedrichs commutator; source 1351-1362, 1556-1583): for `Φ` in the adjoint graph
domain with `(μ + L₀ᵗ)Φ = g` (in distributions, i.e. also against the non-solenoidal tests, using
that `𝒯ᵗ` preserves solenoidality and `g` is solenoidal), `y`-compactly supported, the defect
`(μ + L₀ᵗ)(ρ ⋆ Φ) - ρ ⋆ g` tends to `0` in `Y_2` as the radius of `ρ` tends to `0`
(`ρ ⋆` commutes with `∂_τ`, `Δ`; the commutator with `y·∇` is a Friedrichs commutator on the
compact `y`-support, bounded in `L²` by `‖Φ‖_{Y_2}` and tending to `0`). -/
def MollCommutatorLimit : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ContDiffBump (0 : ℝ × Space), ρ.rOut < δ → ρ.rOut = 2 * ρ.rIn →
        UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - mollP ρ g x) <
            ENNReal.ofReal ε

theorem fwuAdjMoll_of (h1 : MollIsSolTestL) (h2 : MollGraphInYr) (h3 : MollApproxIdentity)
    (h4 : MollCommutatorLimit) : FWUAdjMoll := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ hsupp ε hε
  have he : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, hA⟩ := h3 P hP g hΦ.mem_g _ he
  obtain ⟨δ₂, hδ₂, hB⟩ := h4 P ν μ hP hP1 hν hμ Φ g hΦ hsupp _ he
  set m : ℝ := min δ₁ δ₂ / 2 with hm
  have hmpos : 0 < m := by positivity
  let ρ : ContDiffBump (0 : ℝ × Space) :=
    { rIn := m / 2, rOut := m, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hρ1 : ρ.rOut < δ₁ := by
    show m < δ₁
    have := min_le_left δ₁ δ₂
    rw [hm]; linarith
  have hρ2 : ρ.rOut < δ₂ := by
    show m < δ₂
    have := min_le_right δ₁ δ₂
    rw [hm]; linarith
  obtain ⟨hmeas, hAn⟩ := hA ρ hρ1
  have hBn := hB ρ hρ2 (by show m = 2 * (m / 2); ring)
  have hmem := h2 P ν μ hP hP1 hν hμ Φ g hΦ hsupp ρ
  refine ⟨mollP ρ Φ, h1 P ν μ hP hP1 hν hμ Φ g hΦ hsupp ρ, hmem, ?_⟩
  have htri := phaseLpTri2 P (fun x => L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x)
    (mollP ρ g) g hP hmem.meas hmeas hΦ.mem_g.meas
  calc UnforcedLeray.Short.IIb.phaseLpNorm P 2
        (fun x => L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - g x)
      ≤ _ := htri
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hBn hAn
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add he.le he.le]
        congr 1
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
