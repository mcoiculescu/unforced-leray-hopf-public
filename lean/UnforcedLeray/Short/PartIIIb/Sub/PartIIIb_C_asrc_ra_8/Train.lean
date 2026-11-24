import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.TrainSup
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.HpAL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3.TrainMeas

/-!
# `PartIII-b:C/asrc/ra/8/3` : `RTrainBound` from `RTrainSup`, `HpAL2` and `RTrainMeas`

Source: `the November 2 reference manuscript`
5029-5032, 2040-2051, 4371 (combination in `rTrainBound_of`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rTrainBound (as : ℝ) (χf : ℝ → ℝ) : RTrainBound as χf :=
  rTrainBound_of as χf rTrainSup (_root_.hpAL2 as χf) (_root_.rTrainMeas as χf)

end UnforcedLeray.Short.PartIIIb.Concrete

end
