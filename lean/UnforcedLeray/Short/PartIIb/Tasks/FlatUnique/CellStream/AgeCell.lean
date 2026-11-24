import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!
# Helper for `FlatEqCellStream` (task `PartII-b:T11/1`): the weight-free cell measure

With the weight exponent `a = 0` the age-weighted cylinder measure is the restriction of Lebesgue
measure to `(0, ∞) × cell`, scaled by `c⁻¹` (`Axi.ageμ`, `Cyl.avgμ`, D1 normalization).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CellPart

/-- `ageμ c 0 = c⁻¹ · Lebesgue` restricted to `(0, ∞) × cell c`. -/
theorem ageμ_zero_eq (c : ℝ) :
    UnforcedLeray.Axi.ageμ c 0 =
      ENNReal.ofReal c⁻¹ • (volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.Cyl.cell c)) := by
  unfold UnforcedLeray.Axi.ageμ UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  simp only [Real.rpow_zero, ENNReal.ofReal_one, withDensity_const, one_smul]
  rw [Measure.prod_smul_right, Measure.prod_restrict]
  rfl

end UnforcedLeray.Short.IIb.CellPart
