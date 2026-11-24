import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOfFields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqRealSymm
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.YqOSymm

theorem inletSourcePtw : UnforcedLeray.Short.IIb.InletSourcePtw :=
  UnforcedLeray.Short.IIb.inletSourcePtw_of
    UnforcedLeray.Short.IIb.inletSourceFields
    UnforcedLeray.Short.IIb.yqOfFields
    UnforcedLeray.Short.IIb.yqRealSymm
    UnforcedLeray.Short.IIb.yqOSymm
