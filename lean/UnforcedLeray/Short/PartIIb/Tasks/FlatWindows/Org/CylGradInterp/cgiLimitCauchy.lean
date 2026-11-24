import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.Cauchy.cgiDerivPer
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.Cauchy.cgiCauchyDiff
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.Cauchy.cgiPerLimit

/-!
# `CgiLimitCauchy` (task `PartII-b:T13/1/5/6/1/4`, SP 1932-1933)

Assembles the three leaves `CgiDerivPer`, `CgiCauchyDiff`, `CgiPerLimit` through `cgiLimitCauchy_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cgiLimitCauchy_proof : UnforcedLeray.Short.IIb.CgiLimitCauchy :=
  cgiLimitCauchy_of cgiDerivPer_proof cgiCauchyDiff_proof cgiPerLimit_proof

end UnforcedLeray.Short.IIb
