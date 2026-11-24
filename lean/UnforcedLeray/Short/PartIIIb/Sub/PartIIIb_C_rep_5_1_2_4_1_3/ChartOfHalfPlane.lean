import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/6`: the chart point of a half-plane point

Source `the November 2 reference manuscript` 2672-2674.  Unfolds
`NearInst.chartY`, `NearInst.chartTau`, `NearInst.chartOf`; with `r = ϱ z`,
`√(R²/r²) = R/r`, and the phase is read back modulo the period `2c/R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The chart point of a half-plane point lies in the half plane, with phase read back modulo
the period `2c/R`. -/
theorem chartOfHalfPlane : ChartOfHalfPlane := by
  intro R c z τ hR hc hz
  have hr : 0 < ϱ z := hz
  have hrne : ϱ z ≠ 0 := hr.ne'
  have hRne : R ≠ 0 := hR.ne'
  have hrad : NearInst.hRad z = ϱ z := rfl
  have hs : Real.sqrt (R ^ 2 / ϱ z ^ 2) = R / ϱ z := by
    rw [show R ^ 2 / ϱ z ^ 2 = (R / ϱ z) ^ 2 by rw [div_pow],
      Real.sqrt_sq (by positivity)]
  have hlog : Real.log (R ^ 2 / ϱ z ^ 2) = -(2 * Real.log (ϱ z / R)) := by
    rw [show R ^ 2 / ϱ z ^ 2 = (ϱ z / R)⁻¹ ^ 2 by field_simp]
    rw [Real.log_pow, Real.log_inv]
    push_cast
    ring
  constructor
  · ext i
    fin_cases i
    · simp [NearInst.chartY, NearInst.chartOf, hrad, hs, hRne]
    · simp [NearInst.chartY, NearInst.chartOf, hrad, hs, hRne]
    · simp [NearInst.chartY, NearInst.chartOf, hrad, hs, hRne]
      field_simp
  · refine ⟨⌊(R * Real.log (ϱ z / R) + R * τ / 2) / c + 1 / 2⌋, ?_⟩
    unfold NearInst.chartTau NearInst.chartOf
    simp only [hrad, hlog]
    field_simp
    ring

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
