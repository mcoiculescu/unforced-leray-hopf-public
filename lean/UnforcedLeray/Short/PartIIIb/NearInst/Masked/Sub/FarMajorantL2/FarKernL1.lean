import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# The `L¹` norm of the truncated kernel (source 3999-4000)

`farKern d = |x|^{-4} 1_{|x| ≥ d}` has `L¹(ℝ³)` norm at most `C/d`, by `TailL1`
(the spatial `L¹` tail of `|x|^{-4}` outside distance `d`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem farKernL1_of (hT : TailL1) : FarKernL1 := by
  obtain ⟨C, hC, h⟩ := hT
  refine ⟨C, hC, fun d hd => ?_⟩
  have hS : MeasurableSet {x : UnforcedLeray.Space | d ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  calc ∫⁻ x, farKern d x
      = ∫⁻ x, {x : UnforcedLeray.Space | d ≤ ‖x‖}.indicator
          (fun x => ENNReal.ofReal (‖x‖ ^ (-4 : ℝ))) x :=
        lintegral_congr fun x => by
          unfold farKern
          simp only [Set.indicator_apply, Set.mem_setOf_eq]
    _ = ∫⁻ x in {x : UnforcedLeray.Space | d ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ (-4 : ℝ)) :=
        lintegral_indicator hS _
    _ ≤ ENNReal.ofReal (C / d) := h d hd

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
