import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_8
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceFieldBound.RawProfJet2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceFieldBound.VecDiffJet1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceFieldBound.BEpsJet1

namespace UnforcedLeray.Short.IIb

theorem inletSourceFieldBound_of (hRaw : RawJointSmooth) : InletSourceFieldBound :=
  inletSourceFieldBound_of_leaves hRaw rawProfJet2 vecDiffJet1 bEpsJet1

end UnforcedLeray.Short.IIb
