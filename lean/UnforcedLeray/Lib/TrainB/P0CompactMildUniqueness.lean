import UnforcedLeray.Lib.TrainB.P0CompactMildFixedPoint

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- The actual affine mild equation has at most one solution in the contraction ball. -/
theorem compactActualMildFixedPoint_unique {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (g u v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hfixu : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u)
    (hfixv : v = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v) :
    u = v := by
  have hcontract := norm_projectedNonlinearDuhamelCompactMap_sub_le_half hc hc1 hν hT
    hR hsmall u v hu hv
  let Du := projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u
  let Dv := projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v
  have hdu : u = g + Du := by simpa [Du] using hfixu
  have hdv : v = g + Dv := by simpa [Dv] using hfixv
  have hdist : dist u v = dist Du Dv := by
    calc
      dist u v = dist (g + Du) (g + Dv) :=
        congrArg₂ (fun a b : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => dist a b)
          hdu hdv
      _ = dist Du Dv := by rw [dist_add_left]
  have hcontract' : dist Du Dv ≤ (1 / 2 : ℝ) * dist u v := by
    simpa only [dist_eq_norm] using hcontract
  have hzero : dist u v = 0 := by
    have hle : dist u v ≤ (1 / 2 : ℝ) * dist u v := by
      calc
        dist u v = dist Du Dv := hdist
        _ ≤ (1 / 2 : ℝ) * dist u v := hcontract'
    have hnonneg : 0 ≤ dist u v := dist_nonneg
    nlinarith
  exact eq_of_dist_eq_zero hzero

#print axioms UnforcedLeray.TrainB.compactActualMildFixedPoint_unique

end UnforcedLeray.TrainB
