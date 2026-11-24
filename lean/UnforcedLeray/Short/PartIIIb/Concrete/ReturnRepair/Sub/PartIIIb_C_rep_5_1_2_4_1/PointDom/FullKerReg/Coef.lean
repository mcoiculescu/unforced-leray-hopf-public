import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.SmulBound

/-!
# The cutoff coefficients `χ_y(ν age)` and `deriv χ_y(ν age)·(-2νR²/ϱ³)/ϱ`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  first
  | exact WithTop.coe_le_coe.2 le_top
  | exact (by norm_num : (2 : WithTop ℕ∞) ≤ 3).trans (by exact_mod_cast le_top)
  | simp

theorem ch_contDiffOn {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) (ν R : ℝ) :
    ContDiffOn ℝ 2 (fun y : Space => χ (ν * age R y)) {y | 0 < ϱ y} := by
  have h1 : ContDiffOn ℝ 2 (fun y : Space => ν * age R y) {y | 0 < ϱ y} := by
    unfold age
    exact contDiffOn_const.mul (contDiffOn_const.div (contDiffOn_ϱ_pos.pow 2)
      (fun y hy => (pow_pos hy 2).ne'))
  exact (hχ.smooth.of_le two_le_top).comp_contDiffOn h1

theorem cf_contDiffOn {χ : ℝ → ℝ} (hχ : IsYoungCutoff χ) (ν R : ℝ) :
    ContDiffOn ℝ 2 (fun y : Space => deriv χ (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y)
      {y | 0 < ϱ y} := by
  have h1 : ContDiffOn ℝ 2 (fun y : Space => ν * age R y) {y | 0 < ϱ y} := by
    unfold age
    exact contDiffOn_const.mul (contDiffOn_const.div (contDiffOn_ϱ_pos.pow 2)
      (fun y hy => (pow_pos hy 2).ne'))
  have hd : ContDiff ℝ 2 (deriv χ) :=
    ((contDiff_infty_iff_deriv.1 hχ.smooth).2).of_le two_le_top
  refine ((hd.comp_contDiffOn h1).mul (contDiffOn_const.div (contDiffOn_ϱ_pos.pow 3)
    (fun y hy => (pow_pos hy 3).ne'))).div contDiffOn_ϱ_pos (fun y hy => hy.ne')

end UnforcedLeray.Short.PartIIIb.Concrete

end
