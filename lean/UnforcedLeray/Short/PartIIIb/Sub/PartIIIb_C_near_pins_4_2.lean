import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4

/-!
# `ChartStressIBP`, decomposition (task `PartIII-b:C/near/pins/4/2`)

Source `the November 2 reference manuscript`
1660-1665 (`⟨div T, Φ⟩ = -⟨T, ∇Φ⟩` for the hoop-traction tensor), chart 2666-2668, lift 2683.

* `BandSliceSmooth` : for a band tensor `M`, every slice `y ↦ strPhys M (τ, y) i j` is globally
  smooth and supported in a compact set of the off-axis region `0 < hRad y`.
* `SpaceIBPPairing` : integration by parts on `ℝ³` for a `C¹` complex `g` and a compactly supported
  `C¹` real `f`.
* `ChartSliceIBP` : the slice identity `∫ Φ·F dy = -∫ Σ T_ij ∂_jΦ_i dy` for every `τ`.
`chartStressIBP_of` assembles `ChartStressIBP` from `ChartSliceIBP` (phase average of the slice
identity).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open Set

/-- **Band slices are smooth with compact support off the axis** (source 1660-1665: `M` is a
`C^∞` tensor supported in the band `R/√s₁ ≤ ϱ ≤ R/√s₀`, `|z| ≤ L/√s₀`, `P`-periodic in `τ`). -/
def BandSliceSmooth : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ M : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    ∀ (τ : ℝ) (i j : Fin 3),
      ContDiff ℝ 1 (fun y : Space => strPhys ε⁻¹ c M (τ, y) i j) ∧
      HasCompactSupport (fun y : Space => strPhys ε⁻¹ c M (τ, y) i j) ∧
      (∀ y, strPhys ε⁻¹ c M (τ, y) i j ≠ 0 → 0 < hRad y)

/-- **Integration by parts on `ℝ³`**: `∫ g ∂_j f = -∫ ∂_j g f` for `C¹` `f` (real, compact support)
and `g` (complex, any growth: the product has compact support). -/
def SpaceIBPPairing : Prop :=
  ∀ (f : Space → ℝ) (g : Space → ℂ), ContDiff ℝ 1 f → HasCompactSupport f → ContDiff ℝ 1 g →
    ∀ j : Fin 3,
      ∫ y, g y * ((fderiv ℝ f y (coordinateVector j) : ℝ) : ℂ) =
        -∫ y, fderiv ℝ g y (coordinateVector j) * ((f y : ℝ) : ℂ)

/-- **Slice identity** (source 1660-1665): for each phase `τ`, the slice of `Φ·F` integrates to
`-∫ Σ_{ij} T_ij ∂_jΦ_i` (`T = strPhys M`, `F` the divergence of `T` off the axis; the axis is
Lebesgue null). -/
def ChartSliceIBP : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ M : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    ∀ F : ℝ × Space → CVec3,
      (∀ (τ : ℝ) (y : Space), 0 < hRad y → ∀ i : Fin 3,
        ∑ j : Fin 3, dy j (fun x => ((strPhys ε⁻¹ c M x i j : ℝ) : ℂ)) (τ, y) = F (τ, y) i) →
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ → ∀ τ : ℝ,
        ∫ y, dotL (Φ (τ, y)) (F (τ, y)) =
          -∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
            ((strPhys ε⁻¹ c M (τ, y) i j : ℝ) : ℂ) * dy j Φ (τ, y) i

theorem chartStressIBP_of (h : ChartSliceIBP) : ChartStressIBP := by
  intro c ε hc hε M hM F hF Φ hΦ
  have key := h c ε hc hε M hM F hF Φ hΦ
  unfold pairF stressPair phaseInt
  simp only [key, MeasureTheory.integral_neg, smul_neg]

end UnforcedLeray.Short.PartIIIb.NearInst
