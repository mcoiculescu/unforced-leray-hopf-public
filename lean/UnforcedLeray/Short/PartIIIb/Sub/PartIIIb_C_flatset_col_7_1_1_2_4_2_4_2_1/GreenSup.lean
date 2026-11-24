import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.ConvIntegrable

/-!


Source of record `the November 2 reference manuscript` lines 1713-1716 (the Green
kernel `e^{-|k||η|}/(2|k|)`). `∫ |G_k| = 1/k²`, so a sup bound `M` on the data gives `M/k²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- `∫ e^{-|k||t|} dt = 2/|k|`. -/
theorem gsInt_exp_abs (k : ℝ) (hk : k ≠ 0) :
    ∫ t : ℝ, Real.exp (-|k| * |t|) = 2 / |k| := by
  have hak : 0 < |k| := abs_pos.mpr hk
  have hneg : -|k| < 0 := by linarith
  rw [integral_comp_abs (f := fun s : ℝ => Real.exp (-|k| * s)),
    integral_exp_mul_Ioi hneg 0]
  have hak' : |k| ≠ 0 := ne_of_gt hak
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- **Task target: the Green sup bound** (source 1713-1716). -/
theorem greenSup : GreenSup := by
  intro k hk h M _ hM x
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hak : 0 < |k| := abs_pos.mpr hk
  have hbound : ∀ t : ℝ, ‖(nzGreen k t : ℂ) * h (x.1, x.2 - t)‖
      ≤ (Real.exp (-|k| * |t|) / (2 * |k|)) * M := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hG : |nzGreen k t| = Real.exp (-|k| * |t|) / (2 * |k|) := by
      unfold nzGreen
      rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _),
        abs_of_pos (by positivity : (0 : ℝ) < 2 * |k|)]
    rw [hG]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
  have hI : Integrable (fun t : ℝ => (Real.exp (-|k| * |t|) / (2 * |k|)) * M) :=
    ((nzci_exp_abs_integrable k hk).div_const (2 * |k|)).mul_const M
  have hk2 : k ^ 2 = |k| ^ 2 := (sq_abs k).symm
  show ‖∫ t : ℝ, (nzGreen k t : ℂ) * h (x.1, x.2 - t)‖ ≤ M / k ^ 2
  calc ‖∫ t : ℝ, (nzGreen k t : ℂ) * h (x.1, x.2 - t)‖
      ≤ ∫ t : ℝ, (Real.exp (-|k| * |t|) / (2 * |k|)) * M :=
        norm_integral_le_of_norm_le hI (ae_of_all _ hbound)
    _ = M / k ^ 2 := by
      rw [integral_mul_const, integral_div, gsInt_exp_abs k hk, hk2]
      have hak' : |k| ≠ 0 := ne_of_gt hak
      field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
