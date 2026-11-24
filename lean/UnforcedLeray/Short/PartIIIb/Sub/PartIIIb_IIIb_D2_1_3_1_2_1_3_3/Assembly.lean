import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlIsSolTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.DivIsPhaseTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlCurlId
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.RadialPotential
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.DilKerOK
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.DilLap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ConvTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ConvLap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ConvSub

/-!
# `intertwineLiouville`: assembly

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  `Liou.liouville_of_kernels` (all analytic ingredients proved in
`PartIII-b_IIIb-D2_1_3_1_2_1_3_3.lean`) applied to the nine accepted kernel theorems of
`PartIII-b_IIIb-D2_1_3_1_2_1_3_1_5/` (tasks `PartIII-b:IIIb-D2/1/3/1/2/1/3/1/5/1,2,3,5,6,7,8,9,10`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.Liou

/-- The Liouville step of the stream-potential intertwining (source 1351-1362, 1470-1480). -/
theorem intertwineLiouville_proof : IntertwineLiouville :=
  liouville_of_kernels radialPotential dilKerOK dilLap convTest convLap convSub curlIsSolTest
    divIsPhaseTest curlCurlId

end UnforcedLeray.Short.PartIIIb.Concrete.Liou
