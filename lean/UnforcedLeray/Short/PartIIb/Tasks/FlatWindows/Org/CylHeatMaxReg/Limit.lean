import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit.SubLin
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit.DerivPer
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit.CauchyPer
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit.PairLim
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Limit.IBP

/-!
# Part II-b, task `PartII-b:T13/1/4/4` (`ChmLimit`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935 and
1377-1424. The five leaves `chmSubLin`, `chmDerivPer`, `chmCauchyPer`, `chmPairLim`, `chmIBP` and the
already proved `chmTestDeriv` feed the passage to the limit `chmLimitM_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chmLimit : UnforcedLeray.Short.IIb.ChmLimit :=
  chmLimitM_of chmSubLin chmDerivPer chmCauchyPer chmPairLim chmIBP chmTestDeriv

end UnforcedLeray.Short.IIb
