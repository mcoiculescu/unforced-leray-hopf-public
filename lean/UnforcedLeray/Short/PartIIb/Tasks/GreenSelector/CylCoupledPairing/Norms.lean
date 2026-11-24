import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0610

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.CCP

/-- Unweighted `L²` of the cell is dominated by the weighted norm (`m ≥ 0`). -/
theorem eLpNorm_two_le_Xmc {c m : ℝ} (hm : 0 ≤ m) (w : B0579.X c m) :
    eLpNorm (⇑w) 2 (volume.restrict (B0579.cell c)) ≤ ‖w‖ₑ := by
  rw [Lp.enorm_def, B0579.eLpNorm_cellMeasure]
  refine eLpNorm_mono (fun x => ?_)
  have h1 : (1 : ℝ) ≤ B0579.jb x ^ (m / 2) := by
    apply Real.one_le_rpow _ (by linarith)
    unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (lt_of_lt_of_le one_pos h1)]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

/-- Hölder: the `L¹` norm on the cell is controlled by the weighted norm (`m > 1/2`). -/
theorem eLpNorm_one_le_Xmc {c m : ℝ} (hm : 1 / 2 < m) (w : B0579.X c m) :
    eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun x => B0579.bracket x ^ (-m)) 2 (volume.restrict (B0579.cell c)) * ‖w‖ₑ := by
  have hw : AEStronglyMeasurable (⇑w) (volume.restrict (B0579.cell c)) :=
    (Lp.aestronglyMeasurable w).mono_ac (B0579.ac_cellMeasure c m)
  have hf : AEStronglyMeasurable (fun x => B0579.bracket x ^ m * w x)
      (volume.restrict (B0579.cell c)) :=
    ((B0579.continuous_bracket_rpow m).aestronglyMeasurable).mul hw
  have hφ : AEStronglyMeasurable (fun x => B0579.bracket x ^ (-m))
      (volume.restrict (B0579.cell c)) := (B0579.continuous_bracket_rpow (-m)).aestronglyMeasurable
  have : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf hφ
  have e : ((fun x => B0579.bracket x ^ (-m)) • fun x => B0579.bracket x ^ m * w x) = ⇑w := by
    funext x
    have hb : 0 < B0579.bracket x := Real.sqrt_pos.mpr (B0579.jb_pos x)
    show B0579.bracket x ^ (-m) * (B0579.bracket x ^ m * w x) = w x
    rw [← mul_assoc, ← Real.rpow_add hb, neg_add_cancel,
      Real.rpow_zero, one_mul]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Lp.enorm_def, B0579.eLpNorm_cellMeasure]
  congr 1
  funext x
  rw [B0579.bracket_rpow]

/-- A real constant `C1` with `‖w‖_{L¹(cell)} ≤ C1 ‖w‖_{X_m}`. -/
theorem exists_L1_const (c m : ℝ) (hm : 1 / 2 < m) : ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ w : B0579.X c m,
    eLpNorm (⇑w) 1 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal C1 * ‖w‖ₑ := by
  have hfin := (B0610.memLp_bracket_neg_of_half (c := c) hm).eLpNorm_lt_top
  refine ⟨(eLpNorm (fun x => B0579.bracket x ^ (-m)) 2 (volume.restrict (B0579.cell c))).toReal,
    ENNReal.toReal_nonneg, fun w => ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  exact eLpNorm_one_le_Xmc hm w

end UnforcedLeray.Short.IIb.CCP
