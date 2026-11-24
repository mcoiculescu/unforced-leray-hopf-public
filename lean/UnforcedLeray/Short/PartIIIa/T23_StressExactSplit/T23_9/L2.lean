import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9_2_2

/-!
# Part III-a, task `PartIII-a:T23/9/2`: `ChartSliceMeasurable`

Source: `the November 2 reference manuscript` lines 2703-2711.
The raw half and the inlet half are assembled by `T23_9_Sub.chartSliceMeasurable_of` from the
leaves `greenInverse_measurable_of` (T23/9/2/1), `measurable_primitive_zero` and
`measurable_integral_Ioi` (T23/9/2/1/1, T23/9/2/1/2) and `measurable_ztsum` (T23/9/2/2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem chartSliceMeasurable : UnforcedLeray.Short.IIIa.ChartSliceMeasurable := by
  unfold UnforcedLeray.Short.IIIa.ChartSliceMeasurable
  intro p d dm dp hreg s hs
  exact UnforcedLeray.Short.IIIa.T23_9_Sub.chartSliceMeasurable_of
    (UnforcedLeray.Short.IIIa.T23_9_Sub.greenInverse_measurable_of
      UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_primitive_zero
      UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_integral_Ioi)
    (fun F hF => UnforcedLeray.Short.IIIa.T23_9_Sub.measurable_ztsum F hF)
    p d dm dp hreg s hs

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.chartSliceMeasurable
