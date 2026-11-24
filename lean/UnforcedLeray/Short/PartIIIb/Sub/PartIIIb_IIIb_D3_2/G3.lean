import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAniso
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.ForwardGain
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.Readout
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.GBAdmissible
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Proof
import UnforcedLeray.Short.PartIIIa.T21_FullClock
import UnforcedLeray.Short.Spine.Proofs.TrainEstimates

/-!
# `PartIII-b:IIIb-D3/2/G3`: Assembly of `FlatUnif.GroupOld` (SP 4665–4679)

Assembles `FlatUnif.GroupOld D` from `FlatUnif.G3.flatGroupOld_of`, `flatGroupTested`,
`FlatUnif.G3.oldAnisoTested`, `FlatUnif.G3.earlierOldTested_of`, and the `TrainEstimates`
tuple projections.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem flatGroupOld (D : SeqData) : FlatUnif.GroupOld D :=
  FlatUnif.G3.flatGroupOld_of
    (flatGroupTested D)
    (FlatUnif.G3.oldAnisoTested D)
    (FlatUnif.G3.earlierOldTested_of
      (FlatUnif.G3.forwardGain_of D IIIa.fullClockLongForward)
      (FlatUnif.G3.earlierReadout_of D
        (NearInst.flatTrainMultBound_of
          UnforcedLeray.Short.Spine.trainEstimates.1.2.2.2.2.2.2.1
          UnforcedLeray.Short.Spine.trainEstimates.1.2.2.2.2.2.2.2.1
          UnforcedLeray.Short.Spine.trainEstimates.1.2.2.2.2.2.1))
      (FlatUnif.G1.gBAdmissible D))

end UnforcedLeray.Short.PartIIIb.Concrete
