import UnforcedLeray.Short.PartIIb.Sub.T22_4
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common

/-!
# Leaf `PartII-b:T22/4/1` (`dbInt1`): integrability of `g² w` and `g Δg w` on the cell.

Source: `the November 2 reference manuscript` lines 2092-2104. The decay of
`CylSmoothDecay` (in `η` only) dominates the integrands by `C · jb^{-4}`, which is integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open DbCommon

theorem dbInt1 : UnforcedLeray.Short.IIb.DbInt1 := by
  intro m hm c hc g hg
  have hgc : Continuous g := hg.smooth.continuous
  have hlap : Continuous (lapP g) := continuous_lapP hg.smooth
  have hdens : Continuous (fun x : B0579.Plane => (B0579.density m x : ℝ)) := continuous_dens m
  have hw0 : ∀ x : B0579.Plane, 0 ≤ B0579.jb x ^ m :=
    fun x => Real.rpow_nonneg (B0579.jb_pos x).le m
  constructor
  · refine cell_int_dbS (m := m) (K := 1) hg zero_le_one ((hgc.pow 2).mul hdens) (fun x _ => ?_)
    simp only [B0579.coe_density]
    rw [one_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 x))]
    exact mul_le_mul_of_nonneg_right (sq_le_dbS_mul (abs_le_dbS g x).1) (hw0 x)
  · refine cell_int_dbS (m := m) (K := 1) hg zero_le_one ((hgc.mul hlap).mul hdens)
      (fun x _ => ?_)
    simp only [B0579.coe_density]
    rw [one_mul, abs_mul, abs_mul, abs_of_nonneg (hw0 x)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (abs_le_dbS g x).1 (abs_le_dbS g x).2.2.2 (abs_nonneg _) (dbS_nonneg g x))
      (hw0 x)

end UnforcedLeray.Short.IIb
