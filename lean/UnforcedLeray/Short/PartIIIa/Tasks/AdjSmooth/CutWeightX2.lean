import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.WtCore

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

theorem cutWeightX2 : UnforcedLeray.Short.IIIa.CutWeightX2 := by
  intro c m M χ hmem hM
  have h : ∫ x in B0579.cell c, B0579.jb x ^ (-m) * ‖χ x‖ ^ 2 =
      ∫ x, ‖χ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) :=
    (integral_cellMeasure_eq c m (fun x => ‖χ x‖ ^ 2)).symm
  rw [h, ← sq_toReal_eLpNorm hmem]
  have e0 : 0 ≤ (eLpNorm χ 2 (B0579.cellMeasure c (-m))).toReal := ENNReal.toReal_nonneg
  rcases le_total 0 M with hM0 | hM0
  · have hle : (eLpNorm χ 2 (B0579.cellMeasure c (-m))).toReal ≤ M :=
      ENNReal.toReal_le_of_le_ofReal hM0 hM
    nlinarith [mul_le_mul hle hle e0 hM0]
  · have h0 : eLpNorm χ 2 (B0579.cellMeasure c (-m)) = 0 :=
      le_antisymm (hM.trans_eq (ENNReal.ofReal_of_nonpos hM0)) zero_le
    rw [h0, ENNReal.toReal_zero]
    nlinarith [sq_nonneg M]

end UnforcedLeray.Short.IIIa
