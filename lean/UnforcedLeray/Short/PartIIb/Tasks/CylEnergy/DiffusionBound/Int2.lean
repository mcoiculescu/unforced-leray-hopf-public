import UnforcedLeray.Short.PartIIb.Sub.T22_4
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Short.PartIIb.Sub.T22
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common

/-!
# Leaf `PartII-b:T22/4/2` (`dbInt2`): integrability of `w |∇g|²` and `g ∇w·∇g` on the cell.

Source: `the November 2 reference manuscript` lines 2092-2104. Uses
`|∂_i jb^m| ≤ m jb^m` (`t22_pd_jb_le`) and the decay bound `dbS² jb^m ≤ C jb^{-4}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open DbCommon

theorem dbInt2 : UnforcedLeray.Short.IIb.DbInt2 := by
  intro m hm c hc g hg
  have hgc : Continuous g := hg.smooth.continuous
  have hP : Continuous (B0579.pd 0 g) := continuous_pd_of_c2 hg.smooth 0
  have hQ : Continuous (B0579.pd 1 g) := continuous_pd_of_c2 hg.smooth 1
  have hdens : Continuous (fun x : B0579.Plane => (B0579.density m x : ℝ)) := continuous_dens m
  have hw0 : ∀ x : B0579.Plane, 0 ≤ B0579.jb x ^ m :=
    fun x => Real.rpow_nonneg (B0579.jb_pos x).le m
  constructor
  · refine cell_int_dbS (m := m) (K := 2) hg (by norm_num)
      (hdens.mul ((hP.pow 2).add (hQ.pow 2))) (fun x _ => ?_)
    simp only [B0579.coe_density]
    have hA := sq_le_dbS_mul (abs_le_dbS g x).2.1
    have hB := sq_le_dbS_mul (abs_le_dbS g x).2.2.1
    rw [abs_of_nonneg (mul_nonneg (hw0 x) (add_nonneg (sq_nonneg _) (sq_nonneg _)))]
    have hs : B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2 ≤ 2 * (dbS g x * dbS g x) := by linarith
    calc B0579.jb x ^ m * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)
        ≤ B0579.jb x ^ m * (2 * (dbS g x * dbS g x)) := mul_le_mul_of_nonneg_left hs (hw0 x)
      _ = 2 * (dbS g x * dbS g x * B0579.jb x ^ m) := by ring
  · refine cell_int_dbS (m := m) (K := 2 * m) hg (by linarith) (hgc.mul
      ((continuous_pd0_jb m |>.mul hP).add ((continuous_pd1_jb m).mul hQ))) (fun x _ => ?_)
    have hA := (t22_pd_jb_le hm.le x).1
    have hB := (t22_pd_jb_le hm.le x).2
    have hS := abs_le_dbS g x
    have hmw : 0 ≤ m * B0579.jb x ^ m := mul_nonneg hm.le (hw0 x)
    have hX : |B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
        B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x|
        ≤ (m * B0579.jb x ^ m) * dbS g x + (m * B0579.jb x ^ m) * dbS g x := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul hA hS.2.1 (abs_nonneg _) hmw
      · rw [abs_mul]; exact mul_le_mul hB hS.2.2.1 (abs_nonneg _) hmw
    have key := mul_le_mul hS.1 hX (abs_nonneg _) (dbS_nonneg g x)
    rw [abs_mul]
    exact key.trans (le_of_eq (by ring))

end UnforcedLeray.Short.IIb
