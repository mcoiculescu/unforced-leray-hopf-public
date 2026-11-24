import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Chart

/-!
# The chart phase identity (source 2671-2675)

Proves `ChartTauOf`: `chartTau R (chartOf R c z τ) = τ - k·(2c/R)` with `k` the cell index.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem chartTauOf_proved : ChartTauOf := by
  intro R c z τ hR
  simp only [NearInst.chartTau, NearInst.chartOf]
  by_cases h0 : NearInst.hRad z = 0
  · simp only [h0, zero_div, zero_pow two_ne_zero, div_zero, Real.log_zero, mul_zero,
      add_zero]
    field_simp
    ring
  · have hnn : 0 ≤ NearInst.hRad z := Real.sqrt_nonneg _
    have hpos : 0 < NearInst.hRad z := lt_of_le_of_ne hnn (Ne.symm h0)
    have hlogsq : Real.log (R ^ 2 / NearInst.hRad z ^ 2)
        = 2 * Real.log R - 2 * Real.log (NearInst.hRad z) := by
      rw [Real.log_div (pow_ne_zero 2 hR) (pow_ne_zero 2 hpos.ne'), Real.log_pow,
        Real.log_pow]
      push_cast
      ring
    have hlogq : Real.log (NearInst.hRad z / R)
        = Real.log (NearInst.hRad z) - Real.log R :=
      Real.log_div hpos.ne' hR
    rw [hlogsq, hlogq]
    field_simp
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
