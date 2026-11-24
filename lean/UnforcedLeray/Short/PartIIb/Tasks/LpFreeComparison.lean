import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8

set_option autoImplicit false
noncomputable section

namespace UnforcedLeray.Short.IIb

theorem lpFreeComparison_of (h16 : UnforcedLeray.Short.IIb.HilbertBodyComparison)
    (h18 : UnforcedLeray.Short.IIb.LpInterpolationStep) :
    UnforcedLeray.Short.IIb.LpFreeComparison :=
  lpFreeComparison_of_core h16 h18

end UnforcedLeray.Short.IIb

end
