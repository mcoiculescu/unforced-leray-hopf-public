import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L7
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L8
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L10
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof

/-!
# `PartIII-b:C/ward/13`: `BgPresY2B`

Assembles `bgPresY2B_proved` from `bgPresY2B_of`, `L1`–`L10`, `bgAxiLevels_of`,
and `UnforcedLeray.Short.IIb.strongRegularity_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgPresY2B_proved : BgPresY2B :=
  bgPresY2B_of chartTauOf_proved chartYOf_proved azimuthRot_proved
    (presGradEquivar_of physLapEquivar_proved) presGradCont_proved
    (bgAxiLevels_of UnforcedLeray.Short.IIb.strongRegularity_proof)
    bgUL4_proved bgPresLeray_proved prodL2OfL4_proved lerayComplNormLe_proved

end UnforcedLeray.Short.PartIIIb.Concrete
