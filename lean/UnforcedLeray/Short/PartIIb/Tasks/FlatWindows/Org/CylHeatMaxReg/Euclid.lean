import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Euclid.Real
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Euclid.Split

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem chmEuclid : UnforcedLeray.Short.IIb.ChmEuclid :=
  chmEuclid_of chmEuclidReal chmEuclidSplit

end UnforcedLeray.Short.IIb
