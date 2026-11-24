import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollExists
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollLoc
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollConvNice
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollYoung
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollWeakD2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox

/-!
# `PartII-b:T13/1/5/5` assembly: `CgiMollify`

Source: `the November 2 reference manuscript` lines 1932-1935.
`CgiMollify` follows from the seven leaves via the proved assembly `cgiMollify_of`
(Sub file `PartII-b_T13_1_5_5`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cgiMollify_proof : UnforcedLeray.Short.IIb.CgiMollify :=
  cgiMollify_of mollExists_proof mollLoc_proof mollConvNice_proof mollYoung_proof
    mollDeriv_proof mollWeakD2_proof mollApprox_proof

end UnforcedLeray.Short.IIb
