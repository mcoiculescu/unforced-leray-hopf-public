import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2_1.L4

/-!
# `SepBoxIntegrable` (`PartIII-b:C/near/masked/18/3/4/2/1`)

One application of `sepBoxIntegrable_of` to the four proved hypotheses (A)-(D):
`heatLerayKGradBound` (L1), `boxCartLiftSupport` (L2), `sepBoxMeasurable` (L3),
`sepRadialMajorantIntegrable` (L4).
-/

set_option autoImplicit false

theorem sepBoxIntegrable : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SepBoxIntegrable :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.sepBoxIntegrable_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.boxCartLiftSupport
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.heatLerayKGradBound
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.sepBoxMeasurable
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.sepRadialMajorantIntegrable
