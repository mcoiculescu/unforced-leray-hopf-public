import UnforcedLeray.Units.B0224.Dilation
import UnforcedLeray.Units.B0223.Lift

/-!
# Weighted-norm helpers for the age dilation on `H`

For `s > 0` the weight `s^{-3/2}` of `H` (B0220 `measureH`) equals `(s^{-3/4})^2`, so the map
`F ↦ s^{-3/4} F` is an isometry from `H` to `L²(cellMeasure c)`. These helpers are used by
`Dense.lean` and `Conv.lean` (tex lines 1650-1656).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.DilWeight

open UnforcedLeray.B0220 (Profile cellMeasure measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0224 (lintegral_measureH_eq eLpNorm_two_eq)

theorem enorm_weight_sq {s : ℝ} (hs : 0 < s) (x : MeridC) :
    ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * ‖x‖ₑ ^ 2 = ‖s ^ (-(3 / 4 : ℝ)) • x‖ₑ ^ 2 := by
  have ht : 0 ≤ s ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hs.le _
  have h2 : s ^ (-(3 / 2 : ℝ)) = (s ^ (-(3 / 4 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  rw [h2, ENNReal.ofReal_pow ht, enorm_smul, Real.enorm_eq_ofReal ht, mul_pow]

theorem weight_cancel {s : ℝ} (hs : 0 < s) (x : MeridC) :
    s ^ (-(3 / 4 : ℝ)) • (s ^ (3 / 4 : ℝ) • x) = x := by
  rw [smul_smul, ← Real.rpow_add hs]
  norm_num

theorem scale_identity {s a : ℝ} (hs : 0 < s) (ha : 0 < a) (x y : MeridC) :
    s ^ (-(3 / 4 : ℝ)) • ((a * s) ^ (3 / 4 : ℝ) • x - s ^ (3 / 4 : ℝ) • y) =
      a ^ (3 / 4 : ℝ) • x - y := by
  have hsc : s ^ (-(3 / 4 : ℝ)) * s ^ (3 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]
    norm_num
  rw [Real.mul_rpow ha.le hs.le, smul_sub, smul_smul, smul_smul]
  have e1 : s ^ (-(3 / 4 : ℝ)) * (a ^ (3 / 4 : ℝ) * s ^ (3 / 4 : ℝ)) = a ^ (3 / 4 : ℝ) := by
    calc s ^ (-(3 / 4 : ℝ)) * (a ^ (3 / 4 : ℝ) * s ^ (3 / 4 : ℝ))
        = a ^ (3 / 4 : ℝ) * (s ^ (-(3 / 4 : ℝ)) * s ^ (3 / 4 : ℝ)) := by ring
      _ = a ^ (3 / 4 : ℝ) := by rw [hsc, mul_one]
  rw [e1, hsc, one_smul]

/-- The isometry `F ↦ s^{-3/4} F` from `H` to `L²(cellMeasure c)`. -/
theorem eLpNorm_measureH_eq_weighted {c : ℝ} {H : Profile → MeridC} (hH : StronglyMeasurable H) :
    eLpNorm H 2 (measureH c) =
      eLpNorm (fun p : Profile => p.1 ^ (-(3 / 4 : ℝ)) • H p) 2 (cellMeasure c) := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq, lintegral_measureH_eq _ (hH.enorm.pow_const 2)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with p hp
  exact enorm_weight_sq (show 0 < p.1 from hp.1) (H p)

end UnforcedLeray.Short.PartIIIb.Concrete.DilWeight
