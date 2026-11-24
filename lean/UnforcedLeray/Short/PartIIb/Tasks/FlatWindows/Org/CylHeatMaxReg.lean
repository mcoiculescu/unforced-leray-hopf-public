import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Periodic
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit

/-!
# Part II-b, task `PartII-b:T13/1/4` (`cylHeatMaxReg`): assembly

The three hypotheses of `cylHeatMaxReg_of` are supplied by `CylHeatMaxReg/Periodic.lean`
(`chmPeriodic`), `CylHeatMaxReg/Mollify.lean` (`chmMollify`) and `CylHeatMaxReg/Limit.lean`
(`chmLimit`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylHeatMaxReg : UnforcedLeray.Short.IIb.CylHeatMaxReg :=
  cylHeatMaxReg_of chmPeriodic chmMollify chmLimit

end UnforcedLeray.Short.IIb
