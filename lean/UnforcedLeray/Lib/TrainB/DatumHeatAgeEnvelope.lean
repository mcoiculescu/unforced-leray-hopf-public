import UnforcedLeray.Lib.TrainB.DatumHeatSeedLiteral
import UnforcedLeray.Lib.TrainB.DatumHeatH3OperatorBridge
import UnforcedLeray.Lib.TrainB.P0H3Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace UnforcedLeray.TrainB

open UnforcedLeray.Cyl

/-- Every centered-cell derivative component is bounded by the H³ graph norm. -/
theorem vecH3CellDeriv_norm_le {c : ℝ} (α : Sob.Idx 2 3) (x : VecH3 c) :
    ‖vecH3CellDerivCLM α x‖ ≤ ‖x‖ := by
  change ‖(weightedToCellL2Isometry c)
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α x)‖ ≤ ‖x‖
  rw [(weightedToCellL2Isometry c).norm_map]
  change ‖(x : Sob.SobTuple (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) Vec2 3 2).ofLp α‖ ≤
    ‖(x : Sob.SobTuple (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) Vec2 3 2)‖
  exact PiLp.norm_apply_le (x : Sob.SobTuple
    (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) Vec2 3 2) α

/-- The literal Gaussian heat of the Train datum has a period-independent bound on every
centered-cell derivative component, uniform over every positive age. -/
theorem datumHeatVecH3_component_norm_le {c θ : ℝ} (hc2 : 2 ≤ c) (hθ : 0 < θ)
    (α : Sob.Idx 2 3) :
    ‖vecH3CellDerivCLM α (datumHeatVecH3 hc2 hθ)‖ ≤
      ‖datumVecH3 (by linarith : 0 < c)‖ := by
  rw [datumHeatVecH3_eq_actualHeatVecH3 hc2 hθ]
  calc
    ‖vecH3CellDerivCLM α
        (HeatCylinder.actualHeatVecH3CLM (by linarith : 0 < c) hθ
          (datumVecH3 (by linarith : 0 < c)))‖ ≤
      ‖HeatCylinder.actualHeatVecH3CLM (by linarith : 0 < c) hθ
          (datumVecH3 (by linarith : 0 < c))‖ := vecH3CellDeriv_norm_le α _
    _ ≤ ‖datumVecH3 (by linarith : 0 < c)‖ := by
      calc
        ‖HeatCylinder.actualHeatVecH3CLM (by linarith : 0 < c) hθ
            (datumVecH3 (by linarith : 0 < c))‖ ≤
          ‖HeatCylinder.actualHeatVecH3CLM (by linarith : 0 < c) hθ‖ *
            ‖datumVecH3 (by linarith : 0 < c)‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖datumVecH3 (by linarith : 0 < c)‖ :=
          mul_le_mul_of_nonneg_right
            (HeatCylinder.norm_actualHeatVecH3CLM_le_one (by linarith : 0 < c) hθ)
            (norm_nonneg _)
        _ = _ := one_mul _

#print axioms UnforcedLeray.TrainB.vecH3CellDeriv_norm_le
#print axioms UnforcedLeray.TrainB.datumHeatVecH3_component_norm_le

end UnforcedLeray.TrainB
