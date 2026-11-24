import UnforcedLeray.Loc.L13PhysicalRemainder
import UnforcedLeray.Loc.L01Coefficient
import UnforcedLeray.Loc.L14Realization.TestCalculus
import UnforcedLeray.Loc.L14Realization.Cutoff
import UnforcedLeray.Lib.BochnerTime.Basic

/-!
# H-BgStrong, helpers: the two heat-profile inputs

Support for `Loc/Hyp/BackgroundStrongForm.lean` (target `BackgroundStrongForm` of
`Loc/L13PhysicalRemainder.lean`; `paper/main.tex` lines 159–168 and 275–281; blueprint units
B0707, B0708, B0710).

The reduction of `BackgroundStrongForm` (`backgroundStrongForm_of_heat`) uses, besides
`H2EmbedsC0` of `Loc/L01Coefficient.lean`, facts about the heat profile `H = H_h[u_dss]` alone.
The two stated here have exactly the hypotheses of `HeatProfileRegularity` (the package clauses
on `u_dss`, lines 151–156), so that one proof set-up serves all of them. Both are proved:
`heatProfileGradientL2` in `GradientL2.lean`, `heatProfileEquation` in `HeatEquation.lean`.

* `HeatProfileGradientL2` (lines 275–277): the weak gradient of `H(τ)` lies in `L²` and depends
  continuously on `τ`. The manuscript's bound `|∇H| ≤ C⟨y⟩⁻²` (line 277, uniformly in phase)
  gives `∇H(τ) ∈ L²(ℝ³)`, since `∫⟨y⟩⁻⁴ dy < ∞`; `HeatProfileRegularity` only records
  `∇H ∈ L³`.
* `HeatProfileEquation` (lines 159–163): `H` is a classical solution of
  `∂_τH = hΔH + ½y·∇H + ½H`, tested at every phase: for every vector test `φ`,
  `d/dτ ∫⟨H(τ), φ⟩ = ∫⟨H(τ), hΔφ - φ - ½(y·∇)φ⟩`. (With `s = he^τ`, `λ = e^{τ/2}`, the profile
  `λK_s(λy - x)` of the Dirac mass at `x` solves the equation, and `H` is its superposition
  against `u_dss(x) dx`.) The integrals converge because `H(τ)` is bounded
  (`HeatProfileRegularity`); this file does not rely on the Bochner junk value.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.HypBg

open SobolevGraph
open UnforcedLeray.Blueprint.L13 (radialDeriv)

/-- The vector Laplacian `Δφ = ∑ᵢ ∂ᵢ∂ᵢφ` of a vector test (the form of
`L14.inner_laplace_toL2`). -/
def testLaplacian (φ : Space → Space) : SpatialField :=
  fun x => ∑ i : Fin 3, testPartial (testPartial φ i) i x

/-- The formal adjoint of `𝓛₀ = hΔ + ½y·∇ + ½` applied to a test:
`𝓛₀^*φ = hΔφ - φ - ½(y·∇)φ` (since `(y·∇)^* = -3 - y·∇` on `ℝ³`). -/
def adjointTest (h : ℝ) (φ : Space → Space) : SpatialField :=
  fun y => h • testLaplacian φ y - φ y - (1 / 2 : ℝ) • radialDeriv φ y

/-- **`HeatProfileGradientL2`** (`paper/main.tex` lines 275–277, blueprint B0710; companion of
`HeatProfileRegularity`; proved as `heatProfileGradientL2`). Under the package clauses on `u` (lines
151–156), the heat profile `H(τ) = H_h[u](·, τ)` of lines 159–163 has weak first derivatives
`W(τ)ᵢ ∈ L²(ℝ³;ℝ³)` depending continuously on `τ`. True because `|∇H(y,τ)| ≤ C⟨y⟩⁻²`
locally uniformly in `τ` (line 277) and `∫⟨y⟩⁻⁴ dy < ∞`; continuity from joint continuity of
`∇H` and the uniform tail. -/
def HeatProfileGradientL2 : Prop :=
  ∀ (h period : ℝ) (u : SpatialField), 0 < h → 0 < period → ContDiffOn ℝ ∞ u {0}ᶜ →
    (∀ x : Space, x ≠ 0 → u (Real.exp (period / 2) • x) = Real.exp (-(period / 2)) • u x) →
    (∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ * ‖x‖ ^ (k + 1) ≤ C) →
    ∃ W : ℝ → Fin 3 → L2Space, Continuous W ∧
      ∀ τ i, HasWeakSpatialDerivative i (heatProfile h u τ) (W τ i : SpatialField)

/-- **`HeatProfileEquation`** (`paper/main.tex` lines 159–163, blueprint B0707; proved as
`heatProfileEquation`). Under the package clauses on `u` (lines 151–156), the heat profile
`H(τ) = H_h[u](·, τ)` solves `∂_τH = hΔH + ½y·∇H + ½H` weakly in space at every phase: for
every vector test `φ` and every `τ`,
`d/dτ ∫⟨H(τ,y), φ(y)⟩ dy = ∫⟨H(τ,y), hΔφ(y) - φ(y) - ½(y·∇)φ(y)⟩ dy`. -/
def HeatProfileEquation : Prop :=
  ∀ (h period : ℝ) (u : SpatialField), 0 < h → 0 < period → ContDiffOn ℝ ∞ u {0}ᶜ →
    (∀ x : Space, x ≠ 0 → u (Real.exp (period / 2) • x) = Real.exp (-(period / 2)) • u x) →
    (∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ * ‖x‖ ^ (k + 1) ≤ C) →
    ∀ φ : Space → Space, IsVectorTest φ → ∀ τ : ℝ,
      HasDerivAt (fun σ => ∫ y, inner ℝ (heatProfile h u σ y) (φ y))
        (∫ y, inner ℝ (heatProfile h u τ y) (adjointTest h φ y)) τ

end UnforcedLeray.Blueprint.HypBg
