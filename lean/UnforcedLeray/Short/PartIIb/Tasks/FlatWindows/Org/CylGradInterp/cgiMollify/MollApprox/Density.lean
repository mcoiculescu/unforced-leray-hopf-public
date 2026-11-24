import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Density.Trunc
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Density.StripMemLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Density.WinApprox
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Density.PerzProps
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Density.PerzEst

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem mollApprox_density_proof : UnforcedLeray.Short.IIb.MollDensity :=
  mollApprox_density_proof_of mollTrunc_proof mollStripMemLp_proof mollWinApprox_proof
    mollPerzProps_proof mollPerzEst_proof

end UnforcedLeray.Short.IIb
