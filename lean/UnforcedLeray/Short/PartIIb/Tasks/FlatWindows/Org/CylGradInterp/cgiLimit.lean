import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimitCauchy
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimitWeak
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimitNorm

/-!
# `CgiLimit` (task `PartII-b:T13/1/5/6`, SP 1932-1935)

Assembles the three leaves `CgiLimitCauchy`, `CgiLimitWeak`, `CgiLimitNorm` through `cgiLimit_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cgiLimit_proof : UnforcedLeray.Short.IIb.CgiLimit :=
  cgiLimit_of cgiLimitCauchy_proof cgiLimitWeak_proof cgiLimitNorm_proof

end UnforcedLeray.Short.IIb
