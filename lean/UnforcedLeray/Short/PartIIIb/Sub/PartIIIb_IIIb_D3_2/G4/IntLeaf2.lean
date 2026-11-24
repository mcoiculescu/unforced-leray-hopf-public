import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G4_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoDuhamel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoLinear
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoRem
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBare
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsFinal
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.GBAdmissible
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_3
import UnforcedLeray.Short.PartIIIa.T21_FullClock
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer

/-!
# `PartIII-b:IIIb-D3/2/G4/4/2`: integrable majorant of the upper piece (`flatUpperMaj`)

Assembles `UpperMaj D` from `upperMaj_of_oldAnisoLeaves`, `G3` leaves, `G1` leaves,
and `IIIa` canonical transfer / full-clock results.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

theorem flatUpperMaj (D : SeqData) : UpperMaj D := by
  have hRem := G3.laterOutputRem_of D trainL2Decay_unconditional
    IIIa.fullClockLongForward IIIa.ctKineticImpulse
  exact upperMaj_of_oldAnisoLeaves D
    (G3.duhamelDecomp_of D (FlatUnif.youngSourceFacts D) (G1.gBAdmissible D))
    (G3.oldReadoutLinear D) hRem
    (G3.bareColUnit_of D IIIa.ctMellin IIIa.ctAnisotropy IIIa.fullClockLongForward hRem)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
