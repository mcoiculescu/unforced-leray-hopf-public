import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Short.PartIIIa.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The heat-scaling change of variables on the cells (source 2858-2864, 3030-3035)

`∫_{cell (c/√a)} F(√a y) dy = a⁻¹ ∫_{cell c} F`: the dilation `y ↦ √a • y` maps the cell of
width `c/√a` onto the cell of width `c`, and `Measure.integral_comp_smul` gives the factor `a⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- Scaling of the half-width interval: `r t = c/2` gives the same inequalities after `r ·`. -/
theorem mem_Ico_dilate {r t c y : ℝ} (hr : 0 < r) (ht : r * t = c / 2) :
    (-t ≤ y ∧ y < t) ↔ (-(c / 2) ≤ r * y ∧ r * y < c / 2) := by
  rw [← ht]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- The dilation `y ↦ √a • y` maps the cell of width `c/√a` into the cell of width `c`. -/
theorem mem_cell_dilate {a c : ℝ} (ha : 0 < a) (y : ℝ × ℝ) :
    y ∈ B0579.cell (IIIa.cellLen c a) ↔ (Real.sqrt a) • y ∈ B0579.cell c := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hd : Real.sqrt a * (IIIa.cellLen c a / 2) = c / 2 := by
    unfold IIIa.cellLen
    field_simp
  simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  exact mem_Ico_dilate hr hd

/-- **The heat-scaling change of variables on the cells**, in the form `IntegralCellDilate`. -/
theorem integralCellDilate : IntegralCellDilate := by
  intro F a c ha hc
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hind : (B0579.cell (IIIa.cellLen c a)).indicator (fun y => F (Real.sqrt a * y.1, Real.sqrt a * y.2))
      = fun y => (B0579.cell c).indicator F ((Real.sqrt a) • y) := by
    funext y
    by_cases hy : y ∈ B0579.cell (IIIa.cellLen c a)
    · rw [indicator_of_mem hy, indicator_of_mem ((mem_cell_dilate ha y).1 hy)]
      rfl
    · rw [indicator_of_notMem hy,
        indicator_of_notMem (fun h => hy ((mem_cell_dilate ha y).2 h))]
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    simp [Module.finrank_prod]
  rw [← integral_indicator (B0579.measurableSet_cell (IIIa.cellLen c a)), hind,
    Measure.integral_comp_smul (volume : Measure (ℝ × ℝ)) ((B0579.cell c).indicator F) (Real.sqrt a),
    integral_indicator (B0579.measurableSet_cell c), hfin, hr2,
    abs_of_pos (inv_pos.2 ha), Complex.real_smul, Complex.ofReal_inv]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
