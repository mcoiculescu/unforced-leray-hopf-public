import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.DerivForceSmooth
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatGradIdentity.PsiBounds
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatGradIdentity.PlaneHeatNorm
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatGradIdentity.ContSigma

/-!
# `PartII-a:N01/9/1/2/4/6/2` (assembly): `HeatGradIdentity`

Source `the November 2 reference manuscript`
lines 1684-1689, 3373-3383.  The three analytic facts `HGIPsiBounds`, `HGIPlaneHeatNorm`,
`HGIPlaneHeatContSigma` (proved in the `HeatGradIdentity/` helper files) and the cell-derivative
smoothness `derivForceSmooth` (`DerivForceSmooth.lean`) feed `heatGradIdentity_of_subs`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem heatGradIdentity : UnforcedLeray.Short.PartIIa.N01.HeatGradIdentity :=
  heatGradIdentity_of_subs derivForceSmooth hgiPsiBounds hgiPlaneHeatNorm hgiPlaneHeatContSigma

end UnforcedLeray.Short.PartIIa.N01
