import UnforcedLeray.Units.B0005.Bridge.Unfold
import UnforcedLeray.Units.B0005.Bridge.Weak

/-!
# Interface I10, part 1: integrability of the four pairing terms of a mode

Helper for `Short/Interface/Leaf2_Integrability.lean` (task `Interface:I10`, the pairing clauses
of `ModeSolutionIntegrability`). For `b ∈ 𝒴₂` (`B0005.IsY2`) and a similarity test `ψ`, the terms
`⟨b, ψ⟩`, `⟨b, ∂_τψ⟩`, `⟨b, (y·∇)ψ⟩`, `⟨b, Δψ⟩` are integrable on `ℝ × ℝ³`. Each is
`Blueprint.pairTerm` of a smooth phase test (`ψ`, `dτ ψ`, `radialT ψ`, `lapT ψ`) with a bounded
time window, so the library unfolding `B0005.IsY2.pairTerm_unfold` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface.Leaf2_Integrability

open UnforcedLeray UnforcedLeray.Blueprint

/-- A `𝒴₂` field pairs integrably with a smooth phase test vanishing outside `[-R, R]` in phase. -/
theorem integrable_pairTerm_phaseTest {P : ℝ} (hP : 0 < P) {f : ℝ → SpatialField}
    (hf : B0005.IsY2 P f) {χ : ℝ × Space → Space}
    (hχ : UnforcedLeray.PhaseSpace.IsPhaseTest 0 χ) {R : ℝ} (hR : 0 ≤ R)
    (hRT : UnforcedLeray.PhaseTrace.TimeSupp (-R) R χ) :
    Integrable (pairTerm f χ) := by
  have : Fact (0 < P) := ⟨hP⟩
  exact (hf.pairTerm_unfold hχ (by linarith) hRT).1

/-- `⟨f, ∂_τψ⟩` is the pairing with the phase derivative test. -/
theorem temporalTerm_eq_pairTerm {b : ℝ → SpatialField} {ψ : SpaceTime → Space}
    (hψ : ContDiff ℝ ∞ ψ) : temporalTerm b ψ = pairTerm b (UnforcedLeray.PhaseSpace.dτ ψ) := by
  funext z
  simp only [temporalTerm, pairTerm,
    B0005.dτ_eq_timeDerivative (hψ.differentiable (by simp)) z]

/-- `⟨f, (y·∇)ψ⟩` is the pairing with the radial derivative test. -/
theorem dilationTerm_eq_pairTerm {b : ℝ → SpatialField} {ψ : SpaceTime → Space}
    (hψ : ContDiff ℝ ∞ ψ) :
    dilationTerm b ψ = pairTerm b (UnforcedLeray.PhaseSpace.radialT ψ) := by
  funext z
  simp only [dilationTerm, pairTerm,
    B0005.radialT_eq_spatialDerivative (hψ.differentiable (by simp)) z]

/-- `⟨f, Δψ⟩` is the pairing with the Laplacian test. -/
theorem diffusionTerm_eq_pairTerm {b : ℝ → SpatialField} {ψ : SpaceTime → Space}
    (hψ : ContDiff ℝ ∞ ψ) : diffusionTerm b ψ = pairTerm b (UnforcedLeray.PhaseSpace.lapT ψ) :=
  B0005.diffusionTerm_eq b hψ

/-- The phase derivative of a phase test is a phase test. -/
theorem isPhaseTest_dτ {ψ : ℝ × Space → Space}
    (hψ : UnforcedLeray.PhaseSpace.IsPhaseTest 0 ψ) :
    UnforcedLeray.PhaseSpace.IsPhaseTest 0 (UnforcedLeray.PhaseSpace.dτ ψ) :=
  hψ.fderiv_apply (1, 0)

/-- The radial derivative preserves a time window. -/
theorem timeSupp_radialT' {G : ℝ × Space → Space} {A B : ℝ}
    (hG : UnforcedLeray.PhaseTrace.TimeSupp A B G) :
    UnforcedLeray.PhaseTrace.TimeSupp A B (UnforcedLeray.PhaseSpace.radialT G) := by
  intro τ y hτ
  have hd : ∀ j : Fin 3, UnforcedLeray.PhaseSpace.dy j G (τ, y) = 0 :=
    fun j => B0005.timeSupp_dy hG j τ y hτ
  simp [UnforcedLeray.PhaseSpace.radialT, hd]

/-- **The four pairing terms of a periodic `𝒴₂` mode are integrable against a similarity test.** -/
theorem pairTerms_integrable {P : ℝ} (hP : 0 < P) {b : ℝ → SpatialField}
    (hb : B0005.IsY2 P b) {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    Integrable (pairTerm b ψ) ∧ Integrable (temporalTerm b ψ) ∧
      Integrable (dilationTerm b ψ) ∧ Integrable (diffusionTerm b ψ) := by
  obtain ⟨R, hR0, hRT, -⟩ := B0005.exists_window_of_hasCompactSupport hψ.compact
  have h0 : UnforcedLeray.PhaseSpace.IsPhaseTest 0 ψ := B0005.IsSimilarityTest.isPhaseTest hψ
  refine ⟨integrable_pairTerm_phaseTest hP hb h0 hR0 hRT, ?_, ?_, ?_⟩
  · rw [temporalTerm_eq_pairTerm hψ.smooth]
    exact integrable_pairTerm_phaseTest hP hb (isPhaseTest_dτ h0) hR0
      (B0005.timeSupp_fderiv_apply hRT (1, 0))
  · rw [dilationTerm_eq_pairTerm hψ.smooth]
    exact integrable_pairTerm_phaseTest hP hb h0.radialT hR0 (timeSupp_radialT' hRT)
  · rw [diffusionTerm_eq_pairTerm hψ.smooth]
    exact integrable_pairTerm_phaseTest hP hb h0.lapT hR0 (B0005.timeSupp_lapT hRT)

end UnforcedLeray.Short.Interface.Leaf2_Integrability
