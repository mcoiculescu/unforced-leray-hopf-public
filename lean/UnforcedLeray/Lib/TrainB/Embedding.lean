import UnforcedLeray.Lib.TrainB.CellBridge
import UnforcedLeray.Units.B0151.DivCurl

/-!
# Smooth H²-to-L∞ estimate on the train's centered cylinder cell

This transfers B0151's proved smooth estimate from `(0,c] × ℝ` to the centered unnormalized cell
used by `Cyl.H`. The weak-space extension is a separate density step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane partialX partialY)

/-- Smooth periodic scalar H²-to-L∞ estimate expressed with the centered train-cell norms. -/
theorem smooth_H2_enorm_le_cell {c : ℝ} (hc1 : 1 ≤ c) {f : Plane → ℝ}
    (hfC : ContDiff ℝ 2 f) (hfper : UnforcedLeray.Cyl.IsPeriodic c f)
    (h0 : MemLp f 2 (UnforcedLeray.Cyl.cellμ c))
    (hq : MemLp (partialX f) 2 (UnforcedLeray.Cyl.cellμ c))
    (hη : MemLp (partialY f) 2 (UnforcedLeray.Cyl.cellμ c))
    (hqη : MemLp (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c)) (z : Plane) :
    ‖f z‖ₑ ≤ 3 * (eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialX f) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialY f) 2 (UnforcedLeray.Cyl.cellμ c) +
      eLpNorm (partialY (partialX f)) 2 (UnforcedLeray.Cyl.cellμ c)) := by
  have hc : 0 < c := by linarith
  have hfmeas : Measurable f := hfC.continuous.measurable
  have hxC : ContDiff ℝ 1 (partialX f) :=
    UnforcedLeray.B0151.contDiff_partialX_two hfC
  have hxmeas : Measurable (partialX f) := hxC.continuous.measurable
  have hymeas : Measurable (partialY f) :=
    (UnforcedLeray.B0151.continuous_partialY
      (hfC.of_le (by norm_num))).measurable
  have hxymeas : Measurable (partialY (partialX f)) :=
    (UnforcedLeray.B0151.continuous_partialY hxC).measurable
  have hqper : UnforcedLeray.Cyl.IsPeriodic c (partialX f) := by
    simpa only [UnforcedLeray.Cyl.partialQ_eq_partialX] using hfper.partialQ
  have hηper : UnforcedLeray.Cyl.IsPeriodic c (partialY f) := by
    simpa only [UnforcedLeray.Cyl.partialEta_eq_partialY] using hfper.partialEta
  have hqηper : UnforcedLeray.Cyl.IsPeriodic c (partialY (partialX f)) := by
    simpa only [UnforcedLeray.Cyl.partialEta_eq_partialY,
      UnforcedLeray.Cyl.partialQ_eq_partialX] using hfper.partialQ.partialEta
  have h0b := memLp_b0151_of_cell hc hfmeas hfper h0
  have hqb := memLp_b0151_of_cell hc hxmeas hqper hq
  have hηb := memLp_b0151_of_cell hc hymeas hηper hη
  have hqηb := memLp_b0151_of_cell hc hxymeas hqηper hqη
  have hp : UnforcedLeray.B0151.IsPeriodicQ c f := by
    intro q η
    simpa [UnforcedLeray.Cyl.IsPeriodic] using hfper (q, η)
  have h := UnforcedLeray.B0151.enorm_le_H2 hc1 hfC hp h0b hqb hηb hqηb z
  rw [eLpNorm_sq_b0151_eq_cyl hc hfmeas hfper,
    eLpNorm_sq_b0151_eq_cyl hc hxmeas hqper,
    eLpNorm_sq_b0151_eq_cyl hc hymeas hηper,
    eLpNorm_sq_b0151_eq_cyl hc hxymeas hqηper] at h
  exact h

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.smooth_H2_enorm_le_cell
