import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Band
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Tail.Assembly_IIIb_D3_2_G1_5_2
import UnforcedLeray.Short.Spine.Proofs.TrainEstimates
import UnforcedLeray.Short.PartIIIa.T21_FullClock

/-!
# `PartIII-b:IIIb-D3/2/G1/5`: `laterOutputSource`

Assembles `G1.LaterOutputSource D` from `LaterOutput.laterOutputSource_of`,
`LaterOutput.bandBound_of_partI`, and `LaterOutput.tailBound`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1

theorem laterOutputSource (D : SeqData) : G1.LaterOutputSource D :=
  LaterOutput.laterOutputSource_of D
    (LaterOutput.bandBound_of_partI D
      UnforcedLeray.Short.Spine.trainEstimates.1.2.2.2.2.2.2.1
      UnforcedLeray.Short.Spine.trainEstimates.1.2.2.2.2.2.2.2.1
      UnforcedLeray.Short.Spine.trainEstimates.1.2.2.2.2.2.1
      UnforcedLeray.Short.IIIa.fullClockLongForward)
    (LaterOutput.tailBound D)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1
