import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1_2
import UnforcedLeray.Short.PartI.Tasks.CoupledImpliesFullMild.AmplitudeFreeDuhamel
import UnforcedLeray.Short.PartI.Tasks.CoupledImpliesFullMild.BwdGauge

/-!
# `PartI:C07/1/1/2`: proof of `CoupledImpliesFullMild`

Source `the November 2 reference manuscript`,
lines 1094-1125.  The proof is the assembly `coupledImpliesFullMild_of` of the two leaves
`amplitudeFreeDuhamel` (`PartI:C07/1/1/2/1`) and `bwdGauge` (`PartI:C07/1/1/2/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem coupledImpliesFullMild : UnforcedLeray.Short.PartI.CoupledImpliesFullMild :=
  coupledImpliesFullMild_of amplitudeFreeDuhamel bwdGauge

end UnforcedLeray.Short.PartI
