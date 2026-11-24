import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3.OutChange
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3.Schur
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3.InChange

/-!
# `FarSliceL2` from its three steps (`PartIII-b:C/near/masked/14/2/3`; source 3996-4011, 3604-3610, 2683)

Composes the three proved steps `farOutChange` (`PartIII-b:C/near/masked/14/2/3/1`),
`cartSchur` (`PartIII-b:C/near/masked/14/2/3/2`) and `cartInput` (`PartIII-b:C/near/masked/14/2/3/3`)
through the reduction `farSliceL2_of`.
-/

set_option autoImplicit false

noncomputable section

theorem farSliceL2 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.FarSliceL2 :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.farSliceL2_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.farOutChange
    cartSchur
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.cartInput

end
