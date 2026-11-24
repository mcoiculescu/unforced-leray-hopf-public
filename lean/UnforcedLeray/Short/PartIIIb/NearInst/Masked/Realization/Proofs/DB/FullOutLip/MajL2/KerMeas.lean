import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4

/-!
# Joint measurability of the radial kernel `fmKer` (source 3996-4011)

`fmKer ν l w = ofReal (t^{-2} (1 + |w|/√t)^{-4})` with `t = ν(1-l²)` on `l ∈ (0,1)`, and `0`
otherwise. The indicator of `Ioo 0 1` in `l` is measurable, and the expression is a composition of
measurable real operations (`rpow` with constant exponent, `sqrt`, norm).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fmKerMeasurable : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmKerMeasurable := by
  intro ν
  unfold fmKer
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_Ioo.preimage measurable_fst
  · refine ENNReal.measurable_ofReal.comp ?_
    have ht : Measurable (fun p : ℝ × UnforcedLeray.Space => ν * (1 - p.1 ^ 2)) :=
      measurable_const.mul (measurable_const.sub (measurable_fst.pow_const 2))
    have hs : Measurable (fun p : ℝ × UnforcedLeray.Space => Real.sqrt (ν * (1 - p.1 ^ 2))) :=
      ht.sqrt
    have hA : Measurable (fun p : ℝ × UnforcedLeray.Space =>
        (ν * (1 - p.1 ^ 2)) ^ (-2 : ℝ)) :=
      ht.pow_const _
    have hB : Measurable (fun p : ℝ × UnforcedLeray.Space =>
        (1 + ‖p.2‖ / Real.sqrt (ν * (1 - p.1 ^ 2))) ^ (-4 : ℝ)) :=
      (measurable_const.add ((measurable_snd.norm).div hs)).pow_const _
    exact hA.mul hB

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
