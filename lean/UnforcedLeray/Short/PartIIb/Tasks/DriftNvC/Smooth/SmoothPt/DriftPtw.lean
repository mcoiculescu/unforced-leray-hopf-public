import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2_2
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftOffAxis
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftOnAxis

/-!
# Part II-b, task `PartII-b:T08/1/2/2`: `NvCDriftPtw` from its off-axis and on-axis leaves

Source `the November 2 reference manuscript`, lines 1912-1915.
The composition `nvCDriftPtw_of` (in `Sub/PartIIb_T08_1_2_2.lean`) is applied to the two proved
leaves `nvCDriftOffAxis_proof` and `nvCDriftOnAxis_proof`.
-/

set_option autoImplicit false

noncomputable section

theorem nvCDriftPtw_proof : UnforcedLeray.Short.IIb.NvCDriftPtw :=
  UnforcedLeray.Short.IIb.nvCDriftPtw_of nvCDriftOffAxis_proof nvCDriftOnAxis_proof
