import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Loc.L14Realization.TestCalculus

/-!
# Interface leaf 2 helpers (task `Interface:I11`): test derivatives and the weak mode integrand

Helper file for `Short/Interface/Leaf2.lean`, which proves `periodicModeEquationToLine`.

* The four pairing terms of a similarity test `ψ` (`pairTerm`, `temporalTerm`, `dilationTerm`,
  `diffusionTerm`) are paired against the test derivatives `∂_τψ`, `(y·∇)ψ`, `Δψ`. The
  transfer lemma `PeriodicLineToSlab` (task `Interface:I08`) needs these derivative test functions
  to be continuous and compactly supported; this file proves that from the library's
  `TestCalculus` (`Dt`, `Lap`), using `timeDerivative_eq_Dt`, `spatialDerivative_eq`,
  `spatialLaplacian_eq_Lap`.
* The weak mode integrand splits into the four terms with coefficients `σ + 1`, `-1`, `½`, `-h`
  (`weakModeIntegrand`, `driftAdjointTerm`, lines 176-185 of the shorter proof), and the integral
  of such a linear combination is the linear combination of the integrals.
* `B0005.IsY2 P b` from `IsH1Periodic P b` (the first three clauses of `IsY2Div`).

Source of record: `the November 2 reference manuscript`, lines 176-187 (the mode
equation tested against a periodic test) and lines 6086-6150 (the periodic evolution paragraph).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface.Leaf2

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L14

/-- The time derivative of a similarity test, as a function on `ℝ × ℝ³`, is continuous and
compactly supported. -/
theorem similarity_timeDerivative_regular {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    Continuous (fun z : SpaceTime => timeDerivative ψ z.1 z.2) ∧
      HasCompactSupport (fun z : SpaceTime => timeDerivative ψ z.1 z.2) := by
  have he : (fun z : SpaceTime => timeDerivative ψ z.1 z.2) = Dt ψ := by
    funext z
    exact timeDerivative_eq_Dt hψ.smooth z.1 z.2
  rw [he]
  exact ⟨(contDiff_Dt hψ.smooth).continuous, hasCompactSupport_Dt hψ.compact⟩

/-- The spatial Laplacian of a similarity test, as a function on `ℝ × ℝ³`, is continuous and
compactly supported. -/
theorem similarity_spatialLaplacian_regular {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    Continuous (fun z : SpaceTime => spatialLaplacian ψ z.1 z.2) ∧
      HasCompactSupport (fun z : SpaceTime => spatialLaplacian ψ z.1 z.2) := by
  have he : (fun z : SpaceTime => spatialLaplacian ψ z.1 z.2) = Lap ψ := by
    funext z
    exact spatialLaplacian_eq_Lap hψ.smooth z.1 z.2
  rw [he]
  exact ⟨(contDiff_Lap hψ.smooth).continuous, hasCompactSupport_Lap hψ.compact⟩

/-- The dilation derivative `(y·∇)ψ` of a similarity test, as a function on `ℝ × ℝ³`, is
continuous and compactly supported. -/
theorem similarity_spatialDerivative_regular {ψ : SpaceTime → Space}
    (hψ : IsSimilarityTest ψ) :
    Continuous (fun z : SpaceTime => spatialDerivative ψ z.1 z.2 z.2) ∧
      HasCompactSupport (fun z : SpaceTime => spatialDerivative ψ z.1 z.2 z.2) := by
  have he : (fun z : SpaceTime => spatialDerivative ψ z.1 z.2 z.2) =
      fun z : SpaceTime => fderiv ℝ ψ z ((0 : ℝ), z.2) := by
    funext z
    exact spatialDerivative_eq hψ.smooth z.1 z.2 z.2
  rw [he]
  have hg : ContDiff ℝ ∞ (fun z : SpaceTime => ((0 : ℝ), z.2)) :=
    contDiff_const.prodMk contDiff_snd
  have hC : ContDiff ℝ ∞ (fun z : SpaceTime => fderiv ℝ ψ z ((0 : ℝ), z.2)) :=
    (hψ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply hg
  refine ⟨hC.continuous, HasCompactSupport.intro hψ.compact ?_⟩
  intro z hz
  have h0 : fderiv ℝ ψ z = 0 := by
    by_contra hne
    have hmem : z ∈ Function.support (fderiv ℝ ψ) := hne
    exact hz (support_fderiv_subset (𝕜 := ℝ) hmem)
  simp [h0]

/-- The integral of a four-term linear combination is the linear combination of the integrals,
for integrable terms. -/
theorem integral_four {μ : Measure SpaceTime} (α β γ δ : ℝ) (F₁ F₂ F₃ F₄ : SpaceTime → ℝ)
    (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) (h₃ : Integrable F₃ μ)
    (h₄ : Integrable F₄ μ) :
    ∫ z, (α * F₁ z + β * F₂ z + γ * F₃ z + δ * F₄ z) ∂μ =
      α * ∫ z, F₁ z ∂μ + β * ∫ z, F₂ z ∂μ + γ * ∫ z, F₃ z ∂μ + δ * ∫ z, F₄ z ∂μ := by
  have i1 : Integrable (fun z => α * F₁ z) μ := h₁.const_mul α
  have i2 : Integrable (fun z => β * F₂ z) μ := h₂.const_mul β
  have i3 : Integrable (fun z => γ * F₃ z) μ := h₃.const_mul γ
  have i4 : Integrable (fun z => δ * F₄ z) μ := h₄.const_mul δ
  have i12 : Integrable (fun z => α * F₁ z + β * F₂ z) μ := i1.add i2
  have i123 : Integrable (fun z => α * F₁ z + β * F₂ z + γ * F₃ z) μ := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- The weak mode integrand expands into the four pairing terms with coefficients
`σ + 1`, `-1`, `½`, `-h` (the drift adjoint `-temporalTerm + (3/2)pairTerm + (1/2)dilationTerm`
plus `(σ - 1/2)pairTerm - h diffusionTerm`). -/
theorem weakModeIntegrand_expand (h σ : ℝ) (b : ℝ → SpatialField) (ψ : SpaceTime → Space)
    (z : SpaceTime) :
    weakModeIntegrand h σ b ψ z =
      (σ + 1) * pairTerm b ψ z + (-1) * temporalTerm b ψ z +
        (1 / 2 : ℝ) * dilationTerm b ψ z + (-h) * diffusionTerm b ψ z := by
  unfold weakModeIntegrand driftAdjointTerm
  ring

/-- The integral of the weak mode integrand against a measure on which the four pairing terms
are integrable, as a linear combination of the four integrals. -/
theorem weakModeIntegral_linear {μ : Measure SpaceTime} (h σ : ℝ) (b : ℝ → SpatialField)
    (ψ : SpaceTime → Space)
    (i₁ : Integrable (pairTerm b ψ) μ) (i₂ : Integrable (temporalTerm b ψ) μ)
    (i₃ : Integrable (dilationTerm b ψ) μ) (i₄ : Integrable (diffusionTerm b ψ) μ) :
    ∫ z, weakModeIntegrand h σ b ψ z ∂μ =
      (σ + 1) * ∫ z, pairTerm b ψ z ∂μ + (-1) * ∫ z, temporalTerm b ψ z ∂μ +
        (1 / 2 : ℝ) * ∫ z, dilationTerm b ψ z ∂μ + (-h) * ∫ z, diffusionTerm b ψ z ∂μ := by
  simp only [weakModeIntegrand_expand h σ b ψ]
  exact integral_four (σ + 1) (-1) (1 / 2) (-h) (pairTerm b ψ) (temporalTerm b ψ)
    (dilationTerm b ψ) (diffusionTerm b ψ) i₁ i₂ i₃ i₄

/-- `B0005.IsY2` from the `𝒴₂` clauses of `IsH1Periodic` (`IsY2Div` without solenoidality). -/
theorem isY2_of_isH1Periodic {P : ℝ} {b : ℝ → SpatialField} (hb : IsH1Periodic P b) :
    B0005.IsY2 P b :=
  ⟨hb.value.periodic, hb.value.measurable, hb.value.memL2⟩

end UnforcedLeray.Short.Interface.Leaf2
