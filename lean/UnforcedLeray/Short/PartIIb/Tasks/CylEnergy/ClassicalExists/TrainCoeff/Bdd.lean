import UnforcedLeray.Short.PartIIb.Sub.T22_1_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap

/-!
# Part II-b, task `PartII-b:T22/1/1/2`: the boundedness leaf `TcBdd`

Source: `TrainClose` (`StatementsMixed.lean`) and the cell bound `cylTrainGap`
(`Tasks/CylEnergy/TrainGap.lean`): the velocity is bounded by `C (δ + 1)` on the plane, and
the Euclidean norm of a vector in `ℝ²` is at most the sum of the absolute values of its
two coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIb.CylPDE

theorem tcBdd : UnforcedLeray.Short.IIb.CylPDE.TcBdd := by
  intro Sg hSg ν c δ hν hc hδ tr hcl
  obtain ⟨C, b, hC, hb, hG⟩ := UnforcedLeray.Short.IIb.cylTrainGap Sg hSg
  refine ⟨C * (δ + 1), fun σ hσ x => ?_⟩
  have h := (hG ν c δ hν hc hδ tr hcl σ hσ).1 x
  have hn : ‖tr.v σ x‖ ≤ |tr.v σ x 0| + |tr.v σ x 1| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg (abs_nonneg (tr.v σ x 0)) (abs_nonneg (tr.v σ x 1)),
      sq_abs (tr.v σ x 0), sq_abs (tr.v σ x 1)]
  linarith

end UnforcedLeray.Short.IIb.CylPDE
