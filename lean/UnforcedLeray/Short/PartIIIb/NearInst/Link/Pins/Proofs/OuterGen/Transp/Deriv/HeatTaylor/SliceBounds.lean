import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2_4_13
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.PhaseTestDerivBounded

/-!
# Uniform slice bounds of a phase test (task `PartIII-b:C/near/pins/3/4/2/3/2/4/13/4`)

Proves `ODHT_SliceBounds`.  Route: the slice `y ↦ g(τ, y)` has `k`-th derivative no larger than
`‖D^k g(τ, x)‖` (`HeatGaussEquationAux.slice_norm_le`), and `D^k g` is uniformly bounded for each
`k` by `PartIIa.phaseTestDerivBounded_proof` (compactness of `[0, P] × closedBall 0 R` plus
periodicity and compact `x`-support). Take the sum of the three bounds for `k = 0, 1, 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odhtSliceBounds : ODHT_SliceBounds := by
  intro P _ g hg
  have hP : 0 < P := Fact.out
  obtain ⟨M0, hM0, h0⟩ := UnforcedLeray.Short.PartIIa.phaseTestDerivBounded_proof P hP g hg 0
  obtain ⟨M1, hM1, h1⟩ := UnforcedLeray.Short.PartIIa.phaseTestDerivBounded_proof P hP g hg 1
  obtain ⟨M2, hM2, h2⟩ := UnforcedLeray.Short.PartIIa.phaseTestDerivBounded_proof P hP g hg 2
  refine ⟨M0 + M1 + M2, fun τ k hk x => ?_⟩
  have hs := UnforcedLeray.Short.PartIIa.HeatGaussEquationAux.slice_norm_le hg.smooth τ k x
  refine hs.trans ?_
  interval_cases k
  · exact (h0 (τ, x)).trans (by linarith)
  · exact (h1 (τ, x)).trans (by linarith)
  · exact (h2 (τ, x)).trans (by linarith)

end UnforcedLeray.Short.PartIIIb.NearInst
