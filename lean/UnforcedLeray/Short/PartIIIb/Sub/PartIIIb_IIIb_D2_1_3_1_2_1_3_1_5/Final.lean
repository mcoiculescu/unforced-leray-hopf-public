import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlIsSolTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.DivIsPhaseTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlCurlId
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.PairFSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.WeylL2

/-!
# Leray density in `L²`: assembly (IIIb-D2 1.3.1.2.1.3.1.5)

Assembles `LerayDensityL2` from `lerayDensityL2_of` in the parent module, with the
ingredients `curlIsSolTest`, `divIsPhaseTest`, `curlCurlId`, `pairFSub`, `weylL2`.
Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lerayDensityL2 : UnforcedLeray.Short.PartIIIb.Concrete.LerayDensityL2 :=
  lerayDensityL2_of curlIsSolTest divIsPhaseTest curlCurlId pairFSub weylL2

end UnforcedLeray.Short.PartIIIb.Concrete
