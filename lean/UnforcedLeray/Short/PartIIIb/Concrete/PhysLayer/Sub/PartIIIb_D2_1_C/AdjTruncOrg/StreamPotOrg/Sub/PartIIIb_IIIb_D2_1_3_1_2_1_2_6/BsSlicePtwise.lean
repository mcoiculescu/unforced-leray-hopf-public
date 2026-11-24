import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.BsK2Norm
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncHardyTendsto
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Pointwise bound for the slice Biot-Savart potential (`BsSlicePtwise`)

Source `the November 2 reference manuscript` (stream potential, `L² * |w|⁻² → L⁶`).
`‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ`, `‖a × b‖ ≤ 2‖a‖‖b‖` (`trh_cross_norm`), and `‖bsKernel w‖ = bsK2 w`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsSlicePtwise : BsSlicePtwise := by
  intro F y
  unfold bsSlice rieszT
  have hK : ∀ z : Space, ENNReal.ofReal ‖bsKernel (y - z)‖ = bsK2 (y - z) :=
    fun z => bsK2Norm (y - z)
  calc ENNReal.ofReal ‖∫ z : Space, crossC (F z) (bsKernel (y - z))‖
      = ‖∫ z : Space, crossC (F z) (bsKernel (y - z))‖ₑ := ofReal_norm _
    _ ≤ ∫⁻ z : Space, ‖crossC (F z) (bsKernel (y - z))‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z : Space, 2 * (ENNReal.ofReal ‖F z‖ * bsK2 (y - z)) := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [← ofReal_norm]
        calc ENNReal.ofReal ‖crossC (F z) (bsKernel (y - z))‖
            ≤ ENNReal.ofReal (2 * (‖F z‖ * ‖bsKernel (y - z)‖)) :=
              ENNReal.ofReal_le_ofReal (trh_cross_norm _ _)
          _ = 2 * (ENNReal.ofReal ‖F z‖ * ENNReal.ofReal ‖bsKernel (y - z)‖) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (norm_nonneg _),
                ENNReal.ofReal_ofNat]
          _ = 2 * (ENNReal.ofReal ‖F z‖ * bsK2 (y - z)) := by rw [hK z]
    _ = 2 * ∫⁻ z : Space, ENNReal.ofReal ‖F z‖ * bsK2 (y - z) :=
        lintegral_const_mul' _ _ (by simp)

end UnforcedLeray.Short.PartIIIb.Concrete
