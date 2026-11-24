import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.Order.Group

/-!
# Minkowski inequality for `phaseLr` (task `PartIII-b:C/rep/8/2/pres/4/2/lp/4/1`)

Source `the November 2 reference manuscript` 5134-5139 (`‖F‖_{Y_r}` is the
phase-normalized `L^r` norm of a scalar density on `(0, P] × ℝ³`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `phaseLr` as the `L^r` norm of the product measure, with the constant `ofReal P⁻¹` outside. -/
theorem phaseLr_eq_mul_prod_rpow (P r : ℝ) (hr : 0 ≤ r) {F : ℝ × Space → ℝ} (hF : Measurable F) :
    phaseLr P r F = ENNReal.ofReal P⁻¹ ^ (1 / r) *
      (∫⁻ x, ENNReal.ofReal |F x| ^ r ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume)) ^ (1 / r) := by
  have hm : Measurable fun x : ℝ × Space => ENNReal.ofReal |F x| ^ r :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hF)).pow_const r
  unfold phaseLr
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr)]
  rw [lintegral_prod _ hm.aemeasurable]

/-- **Minkowski for `phaseLr`** (source 5134-5139): `‖F + G‖_{Y_r} ≤ ‖F‖_{Y_r} + ‖G‖_{Y_r}`. -/
theorem phaseLr_add_le {P r : ℝ} (hP : 0 < P) (hr : 1 ≤ r) {F G : ℝ × Space → ℝ} (hF : Measurable F) (hG : Measurable G) : phaseLr P r (fun x => F x + G x) ≤ phaseLr P r F + phaseLr P r G := by
  have hr0 : 0 ≤ r := by linarith
  have hfF : Measurable fun x : ℝ × Space => ENNReal.ofReal |F x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hF)
  have hfG : Measurable fun x : ℝ × Space => ENNReal.ofReal |G x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hG)
  have hpt : ∀ x : ℝ × Space, ENNReal.ofReal |F x + G x| ^ r ≤
      (ENNReal.ofReal |F x| + ENNReal.ofReal |G x|) ^ r := by
    intro x
    apply ENNReal.rpow_le_rpow _ hr0
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
  have hmink := ENNReal.lintegral_Lp_add_le
    (μ := (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space))
    hfF.aemeasurable hfG.aemeasurable hr
  have hI : ∫⁻ x, ENNReal.ofReal |F x + G x| ^ r ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume) ≤
      ∫⁻ x, (ENNReal.ofReal |F x| + ENNReal.ofReal |G x|) ^ r ∂((volume.restrict (Ioc (0 : ℝ) P)).prod volume) :=
    lintegral_mono hpt
  have h1 := le_trans (ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hr0)) hmink
  have hFG : Measurable fun x : ℝ × Space => F x + G x := hF.add hG
  rw [phaseLr_eq_mul_prod_rpow P r hr0 hFG, phaseLr_eq_mul_prod_rpow P r hr0 hF,
    phaseLr_eq_mul_prod_rpow P r hr0 hG, ← mul_add]
  gcongr

end UnforcedLeray.Short.PartIIIb.Concrete
