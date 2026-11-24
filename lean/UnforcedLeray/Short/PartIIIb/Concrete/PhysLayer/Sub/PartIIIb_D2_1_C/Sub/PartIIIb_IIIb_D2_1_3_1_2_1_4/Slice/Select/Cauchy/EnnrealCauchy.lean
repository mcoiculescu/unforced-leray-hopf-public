import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2_props

/-!
# `cEnnrealCauchy`: pure `ℝ≥0∞` Cauchy bookkeeping (source 1351-1362, 1470-1480)

Given `ε > 0`, pick `δ > 0` with `δ * c < ε ^ 2` (`ENNReal.exists_pos_mul_lt`, `c ≠ ⊤`), take `N`
with `x < δ` and `y < 1` beyond `N`; then `z ^ 2 ≤ c * x * y ≤ c * δ < ε ^ 2`, so `z < ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem cEnnrealCauchy : CEnnrealCauchy := by
  intro x y z c hc hx hy hz ε hε
  have hεsq : ε ^ (2 : ℝ) ≠ 0 := (ENNReal.rpow_pos_of_nonneg hε (by norm_num)).ne'
  obtain ⟨δ, hδ, hcδ⟩ := ENNReal.exists_pos_mul_lt hc hεsq
  obtain ⟨N1, hN1⟩ := hx δ hδ
  obtain ⟨N2, hN2⟩ := hy 1 one_pos
  refine ⟨max N1 N2, fun n m hn hm => ?_⟩
  have hxn : x n m < δ := hN1 n m ((le_max_left _ _).trans hn) ((le_max_left _ _).trans hm)
  have hyn : y n m < 1 := hN2 n m ((le_max_right _ _).trans hn) ((le_max_right _ _).trans hm)
  have hkey : c * x n m * y n m ≤ c * δ := by
    calc c * x n m * y n m ≤ c * x n m * 1 := mul_le_mul_of_nonneg_left hyn.le zero_le
      _ = c * x n m := mul_one _
      _ ≤ c * δ := mul_le_mul_of_nonneg_left hxn.le zero_le
  have hsq : z n m ^ (2 : ℝ) < ε ^ (2 : ℝ) := by
    calc z n m ^ (2 : ℝ) ≤ c * x n m * y n m := hz n m
      _ ≤ c * δ := hkey
      _ = δ * c := mul_comm _ _
      _ < ε ^ (2 : ℝ) := hcδ
  exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 hsq

end UnforcedLeray.Short.PartIIIb.Concrete
