import UnforcedLeray.Units.B0224.Semigroup
import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Units.B0223.Lift

/-!
# `HeatIntSliceL2` helper: vector-valued cell contraction of the positive-time plane heat

Same proof as `PlaneHeatCellContract.planeHeat_cell_lintegral_contract`, for a general normed
space `E` (the heat integral takes values in `MeridC`), and for `θ > 0` only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.Short.PartIIa.N01.HeatIntSliceL2Aux

theorem planeHeat_cell_lintegral_contract_E
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {u : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (hu : Continuous u) (hper : ∀ x : ℝ × ℝ, u (x.1 + c, x.2) = u x) :
    ∫⁻ x in UnforcedLeray.B0579.cell c, ‖UnforcedLeray.B0224.planeHeat θ u x‖ₑ ^ 2 ≤
      ∫⁻ x in UnforcedLeray.B0579.cell c, ‖u x‖ₑ ^ 2 := by
  have hcell : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
    simp only [UnforcedLeray.B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  have hup : UnforcedLeray.Cyl.IsPeriodic c u := hper
  have hφm : Measurable fun z : ℝ × ℝ => ‖u z‖ₑ ^ 2 :=
    (hu.measurable.enorm).pow_const 2
  have hφp : UnforcedLeray.Cyl.IsPeriodic c fun z : ℝ × ℝ => ‖u z‖ₑ ^ 2 := by
    intro z
    show ‖u (z.1 + c, z.2)‖ₑ ^ 2 = ‖u z‖ₑ ^ 2
    rw [hper z]
  have hsplit : ∀ x : ℝ × ℝ,
      ‖UnforcedLeray.B0224.planeHeat θ u x‖ₑ ^ 2 ≤
        ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 := by
    intro x
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ u x]
    refine UnforcedLeray.B0224.enorm_integral_gauss_sq_le hθ ?_
    apply Continuous.aestronglyMeasurable
    exact hu.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)
  have hHper : UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.B0224.planeHeat θ u) :=
    UnforcedLeray.B0224.isPeriodic_planeHeat hup
  have hHp : UnforcedLeray.Cyl.IsPeriodic c
      (fun z : ℝ × ℝ => ‖UnforcedLeray.B0224.planeHeat θ u z‖ₑ ^ 2) := by
    intro z
    show ‖UnforcedLeray.B0224.planeHeat θ u (z.1 + c, z.2)‖ₑ ^ 2 =
      ‖UnforcedLeray.B0224.planeHeat θ u z‖ₑ ^ 2
    rw [hHper z]
  rw [hcell]
  calc ∫⁻ x in UnforcedLeray.Cyl.cell c, ‖UnforcedLeray.B0224.planeHeat θ u x‖ₑ ^ 2
      = ∫⁻ x in UnforcedLeray.B0224.strip c, ‖UnforcedLeray.B0224.planeHeat θ u x‖ₑ ^ 2 :=
        (UnforcedLeray.B0224.lintegral_strip_eq_cell hc hHp).symm
    _ ≤ ∫⁻ x in UnforcedLeray.B0224.strip c,
          ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 :=
        lintegral_mono (fun x => hsplit x)
    _ = ∫⁻ x in UnforcedLeray.B0224.strip c, ‖u x‖ₑ ^ 2 :=
        UnforcedLeray.B0224.lintegral_strip_gauss hc hθ hφm hφp
    _ = ∫⁻ x in UnforcedLeray.Cyl.cell c, ‖u x‖ₑ ^ 2 :=
        UnforcedLeray.B0224.lintegral_strip_eq_cell hc hφp

end UnforcedLeray.Short.PartIIa.N01.HeatIntSliceL2Aux
