import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2_4_13
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.Bridge
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.SliceBounds
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.SliceDuhamel

/-!
# Pointwise double Duhamel (task `PartIII-b:C/near/pins/3/4/2/3/2/4/13/6`)

Proves `ODHT_Pointwise` by the one-line assembly `odhtPointwise_of` (proved in the Sub file) applied
to the bridge, slice-bound and slice-Duhamel lemmas.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odhtPointwise : ODHT_Pointwise :=
  odhtPointwise_of odhtBridge odhtSliceBounds odhtSliceDuhamel

end UnforcedLeray.Short.PartIIIb.NearInst
