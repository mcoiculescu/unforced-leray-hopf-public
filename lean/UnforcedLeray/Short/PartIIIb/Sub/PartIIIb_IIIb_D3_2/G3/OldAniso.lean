import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg
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
# `PartIII-b:IIIb-D3/2/G3/1`: Assembly of `OldAnisoTested` (SP 4501–4543, 4665–4676)

Assembles `G3.OldAnisoTested D` from `oldAnisoTested_of` and the four `G3` leaves.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

theorem oldAnisoTested (D : SeqData) : G3.OldAnisoTested D := by
  have hRem := laterOutputRem_of D trainL2Decay_unconditional
    IIIa.fullClockLongForward IIIa.ctKineticImpulse
  exact oldAnisoTested_of D
    (duhamelDecomp_of D (FlatUnif.youngSourceFacts D) (G1.gBAdmissible D))
    (oldReadoutLinear D) hRem
    (bareColUnit_of D IIIa.ctMellin IIIa.ctAnisotropy IIIa.fullClockLongForward hRem)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
