import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/2` (leaf 2: `ChartOfMemStrRegion`)

Source of record: `the November 2 reference manuscript`,
line 2696.  For `|z₃| ≤ Y`, the chart point `chartOf R c z τ = (R²/ϱ², (_, R z₃/ϱ))` satisfies
`|R z₃/ϱ| ≤ Y √(1 + R²/ϱ²)`, using `R/ϱ = √(R²/ϱ²) ≤ √(1 + R²/ϱ²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell)

/-- **Leaf 2** (source 2696): `|R z₃/ϱ| ≤ Y √(1 + R²/ϱ²)` when `|z₃| ≤ Y`. -/
theorem chartOfMemStrRegion_proved : UnforcedLeray.Short.PartIIIb.Concrete.ChartOfMemStrRegion := by
  intro R Y c hR hY z τ hz
  show |R * z 2 / NearInst.hRad z| ≤ Y * Real.sqrt (1 + R ^ 2 / NearInst.hRad z ^ 2)
  have hnn : 0 ≤ Y * Real.sqrt (1 + R ^ 2 / NearInst.hRad z ^ 2) :=
    mul_nonneg hY (Real.sqrt_nonneg _)
  by_cases h0 : NearInst.hRad z = 0
  · have hz0 : |R * z 2 / NearInst.hRad z| = 0 := by
      rw [h0, div_zero, abs_zero]
    rw [hz0]
    exact hnn
  · have hnn' : 0 ≤ NearInst.hRad z := Real.sqrt_nonneg _
    have hpos : 0 < NearInst.hRad z := lt_of_le_of_ne hnn' (Ne.symm h0)
    rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_pos hR]
    have h1 : R * |z 2| / NearInst.hRad z ≤ R * Y / NearInst.hRad z := by
      gcongr
    have h2 : R / NearInst.hRad z = Real.sqrt (R ^ 2 / NearInst.hRad z ^ 2) := by
      rw [← div_pow, Real.sqrt_sq (div_nonneg hR.le hpos.le)]
    have h3 : Real.sqrt (R ^ 2 / NearInst.hRad z ^ 2) ≤
        Real.sqrt (1 + R ^ 2 / NearInst.hRad z ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    calc R * |z 2| / NearInst.hRad z ≤ R * Y / NearInst.hRad z := h1
      _ = Y * (R / NearInst.hRad z) := by ring
      _ = Y * Real.sqrt (R ^ 2 / NearInst.hRad z ^ 2) := by rw [h2]
      _ ≤ Y * Real.sqrt (1 + R ^ 2 / NearInst.hRad z ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hY

end UnforcedLeray.Short.PartIIIb.Concrete
