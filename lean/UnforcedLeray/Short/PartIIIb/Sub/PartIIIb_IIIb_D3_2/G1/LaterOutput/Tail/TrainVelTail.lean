import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoRemOrg

/-!
# `PartIII-b:IIIb-D3/2/G1/5/2/1`: Train velocity cell L² tail bound from `TrainL2Decay`

Source of record: `the November 2 reference manuscript`
lines 4445-4450, 314-317.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

/-- Train velocity cell `L²` tail bound on `s ≥ 2/ν` from `PartI.TrainL2Decay`
(source lines 4445-4450, 314-317). -/
theorem trainVelTailBound_of (D : SeqData) (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay) :
    G1.LaterOutput.TrainVelTailBound D :=
  G3.trainVelTailBound_of_l2Decay D hL2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

end
