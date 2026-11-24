import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WinCut
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowHeatEq
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WeightCompare
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WeakGlue
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DyadicSum

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem flatGraphExists : FlatGraphExists := flatGraphExists_of duhamelFullEq (windowBound_of winCutProps (windowHeatEq_of winCutProps) cylHeatMaxReg cylGradInterp windowWeightCompare) weakGlue dyadicSummation

end UnforcedLeray.Short.IIb
