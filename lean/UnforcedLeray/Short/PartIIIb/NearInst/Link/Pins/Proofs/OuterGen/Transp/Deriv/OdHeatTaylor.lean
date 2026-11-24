import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2_4_13
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.Mink
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.HeatTaylor.Pointwise

/-!
# `odHeatTaylor` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/13`)

Source `the November 2 reference manuscript`
lines 3346-3352 and 1339-1362.  Assembly of the Minkowski step `odhtMink` (task `/2`) and the
pointwise double Duhamel `odhtPointwise` (task `/6`) through `odHeatTaylor_of` (Sub file).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odHeatTaylor : OD_HeatTaylor :=
  odHeatTaylor_of odhtMink odhtPointwise

end UnforcedLeray.Short.PartIIIb.NearInst
