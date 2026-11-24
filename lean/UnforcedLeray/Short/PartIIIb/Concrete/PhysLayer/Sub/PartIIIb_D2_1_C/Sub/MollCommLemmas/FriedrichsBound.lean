import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.FriedrichsBound.KapNonpos
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.FriedrichsBound.KapMean
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.FriedrichsBound.ShiftInv
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.FriedrichsBound.MinkowskiSigned
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_9

/-!
# `friedrichsBound`: the Friedrichs commutator bound (ratio-2 mollifiers)

Source `the November 2 reference manuscript` lines 1556-1583.
Assembles the four ingredients proved in the `FriedrichsBound/` folder through
`friedrichsBound_of` (`Sub/PartIII-b_IIIb-D2_1_3_1_2_2_4_org_9.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem friedrichsBound : FriedrichsBound :=
  friedrichsBound_of kapScale kapIntegrable phaseNormShiftInv phaseMinkowskiSigned

end UnforcedLeray.Short.PartIIIb.Concrete
