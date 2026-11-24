import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_2
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_3
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_4

/-!
# Part II-b, task `PartII-b:P1/1` (`BodyLiftLinear`)

Source of record: `the November 2 reference manuscript` lines 1902-1906.
Assembly of `bodyLiftLinear_of` (`Sub/PartII-b_P1_1.lean`) with the four proved hypotheses
`blRange_proof`, `blUniq_proof`, `blNvLin_proof`, `blRepLin_proof` (leaves `Linear_1..4`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bodyLiftLinear_proof : UnforcedLeray.Short.IIb.BodyLiftLinear :=
  bodyLiftLinear_of blRange_proof blUniq_proof blNvLin_proof blRepLin_proof

end UnforcedLeray.Short.IIb
