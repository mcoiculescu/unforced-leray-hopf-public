import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Euclid
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.Cutoff
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.Leibniz
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.WindowUpper
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.WindowLower
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.CommBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.WeakEq
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic.CoreDeriv

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chmPeriodic : UnforcedLeray.Short.IIb.ChmPeriodic :=
  chmPeriodic_of chmEuclid chmCutoffExists chmLeibniz chmWindowUpper chmWindowLower
    chmCommBound chmWeakEq chmCoreDeriv

end UnforcedLeray.Short.IIb
