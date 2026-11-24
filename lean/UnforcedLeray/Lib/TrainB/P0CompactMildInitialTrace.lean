import UnforcedLeray.Lib.TrainB.P0CompactMildFixedPoint

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- The initial-time point in a nontrivial compact evolution interval. -/
def compactEvolutionZero {T : ℝ} (hT : 0 < T) : Icc (0 : ℝ) T :=
  ⟨0, le_rfl, le_of_lt hT⟩

/-- The actual nonlinear Duhamel term vanishes at initial time because its causal integration
region is empty. -/
theorem projectedNonlinearDuhamelCompactMap_zero {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) :
    projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u (compactEvolutionZero hT) = 0 := by
  rw [projectedNonlinearDuhamelCompactMap_apply]
  simp [compactEvolutionZero, projectedHeatNonlinearityIntegral,
    projectedHeatDuhamelOrbit]

/-- Every fixed point of the compact actual mild map takes exactly its seed value at time zero. -/
theorem compactActualMildFixedPoint_initialTrace {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (g u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hfix : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u) :
    u (compactEvolutionZero hT) = g (compactEvolutionZero hT) := by
  have hzero := projectedNonlinearDuhamelCompactMap_zero hc hc1 hν hT u
  have heval : u (compactEvolutionZero hT) =
      (g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u)
        (compactEvolutionZero hT) := congrArg (fun f :
          ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => f (compactEvolutionZero hT)) hfix
  simpa [hzero] using heval

#print axioms UnforcedLeray.TrainB.projectedNonlinearDuhamelCompactMap_zero
#print axioms UnforcedLeray.TrainB.compactActualMildFixedPoint_initialTrace

end UnforcedLeray.TrainB
