import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoRem
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.GBAdmissible
import UnforcedLeray.Short.PartIIIa.T21_FullClock
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse

/-!
# `PartIII-b:IIIb-D3/2/G1/5/2`: `tailBound`

Standalone assembly file (avoiding the latent import cycle on `LaterOutput/Tail.lean`).
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

theorem tailBound (D : SeqData) : G1.LaterOutput.TailBound D :=
  G3.tailBound_of_laterOutputAbsOp D
    (G3.laterOutputAbsOp_of D
      UnforcedLeray.Short.PartIIIb.Concrete.trainL2Decay_unconditional
      UnforcedLeray.Short.IIIa.fullClockLongForward
      UnforcedLeray.Short.IIIa.ctKineticImpulse)
    (G1.gBAdmissible D)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput
