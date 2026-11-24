import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Chart

/-!
# The chart similarity point identity (source 2671-2675)

Proves `ChartYOf`: off the axis, `chartY R (chartOf R c z τ) = (ϱ(z), 0, z₃)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem chartYOf_proved : ChartYOf := by
  intro R c z τ hR hpos
  have hne : NearInst.hRad z ≠ 0 := hpos.ne'
  have hs : Real.sqrt (R ^ 2 / NearInst.hRad z ^ 2) = R / NearInst.hRad z := by
    rw [← div_pow, Real.sqrt_sq (div_pos hR hpos).le]
  simp only [NearInst.chartY, NearInst.chartOf, hs]
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
