import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj

theorem inletSourceBound : UnforcedLeray.Short.IIb.InletSourceBound :=
  UnforcedLeray.Short.IIb.inletSourceBound_of
    inletSourcePtw
    UnforcedLeray.Short.IIb.lerayForceProj
