import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.Mdk1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MdkAsm
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.Mdk2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.Mdk3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.Mdk4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.Mdk5

/-!
# `MollDivKernel` (divergence of the mollification via the periodised reflected kernel)

Source: `the November 2 reference manuscript`
lines 1351-1362. Assembles `mollDivKernel_of` from the phase-test property `perKPhaseTest` (Mdk1)
and the divergence identity `divIdentity_of` (MdkAsm, fed by Mdk2-Mdk5).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollDivKernel : MollDivKernel :=
  mollDivKernel_of perKPhaseTest (divIdentity_of dyMollP foldCell dyPerK phaseIntCell)

end UnforcedLeray.Short.PartIIIb.Concrete
