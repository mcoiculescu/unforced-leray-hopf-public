import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1.Norm
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_P1_1_1.Lift
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.Real
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.Axi
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.PerAE
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_1.Congr

/-!
# `PartII-b:P1/1/1/1`-`4` assembled: `BLRange` (`PartII-b:P1/1/1`).

Source of record: `the November 2 reference manuscript` lines 1902-1906.
Assembly of `blRange_of` (`Sub/PartII-b_P1_1_1.lean`) with the proved hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem blRange_proof : BLRange :=
  blRange_of blrReal_proof blrAxi_proof (blrLift_of blrPerAE_proof) blrNorm_proof blrCongr_proof

end UnforcedLeray.Short.IIb
