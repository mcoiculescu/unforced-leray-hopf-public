import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_1_org
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB3s
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB1c

/-!
# `PartIII-a:T21/c3/2/1/2/2/1/2/2/1`: leaf `RelB1`

Source of record: `the November 2 reference manuscript` (SP).
Route: `relB1_of` combines the leaf `RelB3s` with the leaf `RelB1c`.
-/

set_option autoImplicit false

theorem relB1_leaf (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) : UnforcedLeray.Short.IIIa.RelRegularityOrg.RelB1 κ :=
  UnforcedLeray.Short.IIIa.RelRegularityOrg2.relB1_of κ
    (UnforcedLeray.Short.IIIa.RelRegularityOrg2.relB3s_leaf κ)
    (UnforcedLeray.Short.IIIa.RelRegularityOrg2.relB1c_leaf κ)
