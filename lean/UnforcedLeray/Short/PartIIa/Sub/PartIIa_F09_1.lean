import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09
import UnforcedLeray.Units.B0421.Phase

/-!
# Part II-a, task `PartII-a:F09/1`: existence of the adjoint resolvent at `r = 2`

Source `the November 2 reference manuscript`, lines 1359-1361 (`L^* = -𝒯 - νΔ + 1`
at `r = 2`), 1403-1413 (the adjoint semigroup `S(t)^* h = e^{-t}[e^{ν(1-e^{-t})Δ}h](e^{-t/2}y)`
and the adjoint resolvent) and 1426-1440 (time reversal, `a_2 = Re μ + 1/4`).

`adjT ν t` is the Hilbert-space adjoint on `Y_2` of the phase-translated free semigroup
`phaseT ν t`, i.e. `S(t)^*` composed with the reversed phase translation. Its pointwise formula
is the content of `PartII-a:F02/3` (`adjointFormula`); here only the three analytic statements
about the Laplace integral are isolated, and `AdjointExistence` is derived from them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **The adjoint free semigroup on `Y_2`** (lines 1405, 1426-1428): the Hilbert adjoint of
`𝒯(t) = phaseT ν t`, `(𝒯(t) g)(τ) = S_ν(t) g(τ - t)`. Slicewise it is
`S(t)^* h = e^{-t}[e^{ν(1-e^{-t})Δ}h](e^{-t/2}y)` followed by the phase translation `τ ↦ τ + t`. -/
def adjT (P : ℝ) [Fact (0 < P)] (ν t : ℝ) : Yq P 2 →L[ℂ] Yq P 2 :=
  ContinuousLinearMap.adjoint (B0421.phaseT (P := P) (q := 2) ENNReal.ofNat_ne_top ν t)

/-- **Semigroup bound, strong continuity, semigroup law** for `S(t)^*` (lines 1405-1406: "by the
gap", `‖S(t)^*‖ ≤ e^{-t/4}` since `γ_2 = 1/4`). -/
def AdjSemigroupBound : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν →
    (∀ t : ℝ, 0 ≤ t → ‖adjT P ν t‖ ≤ Real.exp (-t / 4)) ∧
    (∀ f : Yq P 2, ContinuousOn (fun t : ℝ => adjT P ν t f) (Set.Ici 0)) ∧
    adjT P ν 0 = 1 ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → adjT P ν (s + t) = (adjT P ν t).comp (adjT P ν s))

/-- **Existence of the adjoint resolvent** (lines 1426-1440): for `Re μ + 1/4 > 0` the Laplace
integral `R f = ∫₀^∞ e^{-μ̄ t} S(t)^* f dt` defines a bounded operator with
`‖R‖ ≤ (Re μ + 1/4)^{-1}`. -/
def AdjResolventExists : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∃ Rm : Yq P 2 →L[ℂ] Yq P 2, ‖Rm‖ ≤ (μ.re + 1 / 4)⁻¹ ∧
      ∀ f, Rm f = ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-((starRingEnd ℂ) μ * t)) • adjT P ν t f

/-- **The adjoint resolvent solves the adjoint equation** (lines 1426-1440): the Laplace integral
`R f` satisfies `(μ̄ + L₀^{*}) R f = f` in distributions, i.e. `HasPhaseOp (μ̄ + L₀) (R f) f`
(the transpose of `μ̄ + L^*` on phase tests is `μ̄ + L₀`). -/
def AdjResolventEquation : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ Rm : Yq P 2 →L[ℂ] Yq P 2,
      (∀ f, Rm f = ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-((starRingEnd ℂ) μ * t)) • adjT P ν t f) →
      ∀ f, HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) (Rm f) f

/-- `AdjointExistence` from the three statements above. -/
theorem adjointExistence_of (_h1 : AdjSemigroupBound) (h2 : AdjResolventExists)
    (h3 : AdjResolventEquation) : AdjointExistence := by
  intro P _ _ ν hν μ hμ f
  obtain ⟨Rm, _, hRm⟩ := h2 P ν hν μ hμ
  exact ⟨Rm f, h3 P ν hν μ hμ Rm hRm f⟩

end UnforcedLeray.Short.PartIIa
