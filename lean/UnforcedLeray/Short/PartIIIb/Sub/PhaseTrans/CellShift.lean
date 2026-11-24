import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `PhaseCellShift`: shifting the phase cell into the time box

Source `the November 2 reference manuscript`
lines 1556-1583. For `|z₁| ≤ 1`, the translate `x ↦ x - z` maps the base cell `(0,P] × ℝ³` into
`[-(P+1), P+1] × ℝ³ = tBox (P+1)`, and translation invariance of `volume` on `ℝ × ℝ³` gives
the bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phaseCellShift : PhaseCellShift := by
  intro P hP h z hz
  have : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hT : MeasurableSet (tBox (P + 1)) := measurableSet_Icc.prod MeasurableSet.univ
  calc ∫⁻ x, ‖h (x - z)‖ₑ ^ (2 : ℝ) ∂(muP P)
      = ∫⁻ x, (cellBase P).indicator (fun x => ‖h (x - z)‖ₑ ^ (2 : ℝ)) x := by
        rw [muP_eq_cellBase, lintegral_indicator (measurableSet_cellBase P)]
    _ ≤ ∫⁻ x, (tBox (P + 1)).indicator (fun x => ‖h x‖ₑ ^ (2 : ℝ)) (x - z) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ cellBase P
        · have hmem : x - z ∈ tBox (P + 1) := by
            have hx' := hx
            simp only [cellBase, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true] at hx'
            have hza := abs_le.mp hz
            simp only [tBox, Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true, Prod.fst_sub]
            constructor <;> linarith [hx'.1, hx'.2, hza.1, hza.2]
          rw [Set.indicator_of_mem hx]
          rw [Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ∫⁻ x, (tBox (P + 1)).indicator (fun x => ‖h x‖ₑ ^ (2 : ℝ)) x :=
        lintegral_sub_right_eq_self (fun x => (tBox (P + 1)).indicator
          (fun x => ‖h x‖ₑ ^ (2 : ℝ)) x) z
    _ = ∫⁻ x in tBox (P + 1), ‖h x‖ₑ ^ (2 : ℝ) := lintegral_indicator hT _

end UnforcedLeray.Short.PartIIIb.Concrete
