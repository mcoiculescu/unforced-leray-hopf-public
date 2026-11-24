import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Of
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSDefined
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGrad
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSCurl
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSSol
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSSlice
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.HardyR3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSHardyY2

/-!
# `StreamPotExists` from the Biot-Savart ingredients

Source `the November 2 reference manuscript` lines 1351-1362.
The seven ingredients are proved in the `StreamPotOrg/` lemma modules and assembled by
`streamPotExists_of` (`StreamPotOrg/Of.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem streamPotExists : StreamPotExists :=
  streamPotExists_of bsDefined bsGrad bsCurl bsSol hardyR3 UnforcedLeray.Short.PartIIIb.bsSlice bsHardyY2

end UnforcedLeray.Short.PartIIIb.Concrete
