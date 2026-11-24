import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.MomentsOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NearUnit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.Bclass
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.ActualSeq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FrakTOldFinite

/-!
# `PartIII-b:IIIb-D3/2/G5/3`: Assembly of `FrakTMoments` (SP 4637–4640, 4686–4693, 4757–4760, 4848–4854, 4917–4927)

Assembles `FlatUnif.G5.FrakTMoments D` from `frakTMoments_of` and the six leaf theorems.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

theorem frakTMoments (D : SeqData) : FlatUnif.G5.FrakTMoments D :=
  frakTMoments_of D
    (flatGroupYoung D)
    (flatGroupTested D)
    (flatNearUnit D)
    G6.bmatBclass
    (G6.actualSeqPinned D)
    frakTOldFinite

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
