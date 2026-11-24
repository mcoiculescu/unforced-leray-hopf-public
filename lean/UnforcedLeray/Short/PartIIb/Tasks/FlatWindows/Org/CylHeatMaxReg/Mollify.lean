import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Nice
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Eq
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.Conv

/-!
# Part II-b, task `PartII-b:T13/1/4/3` (`ChmMollify`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935.
The leaves `chmMollNice`, `chmMollEq`, `chmMollConv` feed `chmMollify_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chmMollify : UnforcedLeray.Short.IIb.ChmMollify :=
  chmMollify_of chmMollNice chmMollEq chmMollConv

end UnforcedLeray.Short.IIb

end
