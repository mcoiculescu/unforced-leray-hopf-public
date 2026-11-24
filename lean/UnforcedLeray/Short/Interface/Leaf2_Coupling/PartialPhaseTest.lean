import UnforcedLeray.Short.Interface.Sub.I09

/-!
# Interface:I09 sub-lemma: a spatial partial derivative of a similarity test is a phase test

Source of record: `the November 2 reference manuscript`, lines 173-180 (the tests
for the mode equation are smooth with compact support). The statement is `SimilarityPartialPhaseTest`
from `Short/Interface/Sub/I09.lean`: for a similarity test `ψ` and a direction `j`, the function
`(τ, y) ↦ ∂ⱼψ(τ, y)` is a phase test with a time window `[-R, R]`, and it agrees with the
spatial partial derivative of the slice `ψ(τ, ·)`.

Proof: `ψ` has compact support, so it has a time window `R`. The phase test is the
directional derivative `fderiv ℝ ψ _ (0, coordinateVector j)` of the phase test `ψ`, and the
identity with `testPartial (slice ψ τ) j` is `dy_eq_spatialDerivative`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- **Sub-lemma I09/3.** A spatial partial derivative of a similarity test is a phase test with a
time window (source lines 173-180). -/
theorem similarityPartialPhaseTest : SimilarityPartialPhaseTest := by
  intro ψ hψ j
  obtain ⟨R, hR0, hRT, -⟩ := B0005.exists_window_of_hasCompactSupport hψ.compact
  refine ⟨R, hR0, UnforcedLeray.PhaseSpace.dy j ψ, ?_, B0005.timeSupp_dy hRT j, fun τ y => ?_⟩
  · exact (B0005.IsSimilarityTest.isPhaseTest hψ).fderiv_apply (0, coordinateVector j)
  · exact B0005.dy_eq_spatialDerivative (hψ.smooth.differentiable (by simp)) (τ, y) j

end UnforcedLeray.Short.Interface
