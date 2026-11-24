import UnforcedLeray.Short.PartIIa.StatementsFree

/-!
# Part II-a, task `PartII-a:F09`: decomposition of the adjoint at `r = 2`

Source `the November 2 reference manuscript` lines 1359-1361 and 1426-1442
(adjoint equation `(μ̄ - 𝒯 - νΔ + 1) w = f`, time reversal of the body problem).
`CommonBodyAdjoint` is the conjunction of existence, maximal-domain membership and the graph bound.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Adjoint existence (lines 1426-1440, adjoint semigroup `S(t)*`). -/
def AdjointExistence : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ f : Yq P 2, ∃ w : Yq P 2,
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f

/-- Adjoint maximal domain (time reversal of `commonBodyMaximalDomain`, lines 1409-1412, 1432-1442). -/
def AdjointMaximalDomain : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ w f : Yq P 2,
      HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f → w ∈ D P ν 2

/-- Adjoint graph bound (time reversal of `commonBodyGraphBound` at `r = 2`, Hilbert identity). -/
def AdjointGraphBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
      ∀ f : Yq P 2, ∀ w : Yq P 2,
        HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
        ∀ hw : w ∈ D P ν 2, ∃ g : Fin 3 → Yq P 2, HasGrad w g ∧
          graphNormD (⟨w, hw⟩ : D P ν 2) + Real.sqrt ν * ∑ j, ‖g j‖ ≤
            C * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ‖f‖

theorem commonBodyAdjoint_of (h1 : AdjointExistence) (h2 : AdjointMaximalDomain)
    (h3 : AdjointGraphBound) : CommonBodyAdjoint := by
  obtain ⟨C, hC, hb⟩ := h3
  refine ⟨C, hC, fun P _ hP ν hν μ hμ f => ⟨h1 P hP ν hν μ hμ f, fun w hw => ?_⟩⟩
  have hD := h2 P hP ν hν μ hμ w f hw
  obtain ⟨g, hg, hle⟩ := hb P hP ν hν μ hμ f w hw hD
  exact ⟨hD, g, hg, hle⟩

end UnforcedLeray.Short.PartIIa
