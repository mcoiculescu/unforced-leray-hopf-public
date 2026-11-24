import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollLoc
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollYoung
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollConvNice
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Density
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollApprox.Nice

/-!
# `PartII-b:T13/1/5/5/7` assembly: approximate identity `MollApprox`

Source: `the November 2 reference manuscript` lines 1932-1935.
`MollApprox` follows from the assembly `mollApprox_of` (Sub file) applied to the leaves
`mollLoc_proof`, `mollYoung_proof`, `mollApprox_density_proof`, `mollApprox_nice_proof`,
`mollConvNice_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem mollApprox_proof : UnforcedLeray.Short.IIb.MollApprox :=
  mollApprox_of mollLoc_proof mollYoung_proof mollApprox_density_proof mollApprox_nice_proof
    mollConvNice_proof

end UnforcedLeray.Short.IIb
