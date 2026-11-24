import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjCommuteProps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.L0TAddSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.L0TGradComm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.SigmaDecay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.GradPairingGeneral

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1`: commutation of `L₀ᵗ` with the Leray projection (smooth form)

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Assembles `L0TProjSmoothCommute` from the accepted leaves
`l0TAddSmooth`, `l0TGradComm`, `sigmaDecay`, `gradPairingGeneral` via `l0TProjSmoothCommute_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l0TProjSmoothCommute : L0TProjSmoothCommute :=
  l0TProjSmoothCommute_of (l0TGradAdd_of l0TAddSmooth l0TGradComm)
    (projGradSliceTest_of sigmaDecay gradPairingGeneral)
    (gradPairingVanish_of sigmaDecay gradPairingGeneral)

end UnforcedLeray.Short.PartIIIb.Concrete
