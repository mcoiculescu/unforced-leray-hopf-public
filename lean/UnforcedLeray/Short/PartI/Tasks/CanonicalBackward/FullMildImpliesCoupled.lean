import UnforcedLeray.Short.PartI.Sub.PartI_C08_1_3
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.FullMildToBwd
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.BwdGaugeConverse
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.AmplitudeConverse
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.ComplementConverse
import UnforcedLeray.Short.PartI.Tasks.CoupledImpliesFullMild.AmplitudeFreeDuhamel

/-!
# `PartI:C08/1/3`: proof of `FullMildImpliesCoupled`

Source `the November 2 reference manuscript`
lines 1094-1125.  The four leaf proofs and `AmplitudeFreeDuhamel` are composed through
`fullMildImpliesCoupled_of` (`Sub/PartI_C08_1_3.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray MeasureTheory Set

/-- **`FullMildImpliesCoupled`** (lines 1094-1125): composition of the four converse leaves and
`AmplitudeFreeDuhamel`. -/
theorem fullMildImpliesCoupled_proof : UnforcedLeray.Short.PartI.FullMildImpliesCoupled :=
  fullMildImpliesCoupled_of fullMildToBwd_proof bwdGaugeConverse_proof amplitudeConverse_proof
    complementConverse_proof amplitudeFreeDuhamel

end UnforcedLeray.Short.PartI
