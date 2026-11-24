import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.PairFSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.RadialPotential
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.DilKerOK
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.DilLap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ConvTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ConvLap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.ConvSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.SmallScale
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.LargeScale

/-!
# Weyl's lemma in `L²`: assembly

Assembles `WeylL2` from the nine proved ingredients (`RadialPotential`, `DilKerOK`, `DilLap`,
`ConvTest`, `ConvLap`, `ConvSub`, `SmallScale`, `LargeScale`, `PairFSub`) via `weylL2_of`
in the parent module (source lines 1351-1362, 1470-1480).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem weylL2 : UnforcedLeray.Short.PartIIIb.Concrete.WeylL2 :=
  weylL2_of radialPotential dilKerOK dilLap convTest convLap convSub smallScale largeScale
    pairFSub

end UnforcedLeray.Short.PartIIIb.Concrete
