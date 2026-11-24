import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawDivFree
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceRealO
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceIBP
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceGradPtw
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourcePerMeas
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceFieldBound

/-!
# Part II-b, task `PartII-b:G4/4/1/1`: `InletSourceFields`

Assembles `inletSourceFields : InletSourceFields` from `inletSourceFields_of` and the seven leaf
modules under `Fields/`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem inletSourceFields : UnforcedLeray.Short.IIb.InletSourceFields :=
  inletSourceFields_of
    (inletSourceRealO_of rawJointSmooth)
    (inletSourceIBP_of rawJointSmooth rawDivFree)
    (inletSourceGradPtw_of rawJointSmooth)
    (inletSourcePerMeas_of rawJointSmooth)
    (inletSourceFieldBound_of rawJointSmooth)

end UnforcedLeray.Short.IIb
