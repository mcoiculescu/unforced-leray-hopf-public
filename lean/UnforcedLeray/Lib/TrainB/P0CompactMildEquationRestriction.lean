import UnforcedLeray.Lib.TrainB.P0CompactDuhamelRestriction

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- A genuine compact-time mild equation restricts to every shorter interval: its seed restricts
pointwise, and the actual nonlinear Gaussian Duhamel term is causal. -/
theorem compactMildEquation_restrict {c ν T S : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν)
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hTS : T ≤ S)
    (g u : ContinuousMap (Icc (0 : ℝ) S) (VectorH3 c))
    (hfix : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hS u) :
    restrictCompactEvolutionPath hTS u =
      restrictCompactEvolutionPath hTS g +
        projectedNonlinearDuhamelCompactMap hc hc1 hν hT
          (restrictCompactEvolutionPath hTS u) := by
  apply ContinuousMap.ext
  intro t
  have hD := projectedNonlinearDuhamelCompactMap_restrict hc hc1 hν hTS u t
  have hfixAt := congrArg (fun f : ContinuousMap (Icc (0 : ℝ) S) (VectorH3 c) =>
    f (compactIntervalInclusion hTS t)) hfix
  calc
    u (compactIntervalInclusion hTS t) =
        g (compactIntervalInclusion hTS t) +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hS u
            (compactIntervalInclusion hTS t) :=
      hfixAt
    _ = g (compactIntervalInclusion hTS t) +
        projectedNonlinearDuhamelCompactMap hc hc1 hν hT
          (restrictCompactEvolutionPath hTS u) t :=
      congrArg (fun z : VectorH3 c => g (compactIntervalInclusion hTS t) + z) hD.symm

#print axioms UnforcedLeray.TrainB.compactMildEquation_restrict

end UnforcedLeray.TrainB
