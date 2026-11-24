import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrTrainClose
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrTransfer
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical

/-!
# Part III-a, task `PartIII-a:T21/c2/2`: `FmeRate`

Source of record: `the November 2 reference manuscript`, lines 2937-2958.
Assembles `fmeRate : FmeRate` from `fmeRate_of`, `fmrTrainClose`, `cylClassicalExists`,
`cylWeakEqClassical`, `fmrRegular`, and `fmrTransfer`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem fmeRate : FmeRate :=
  fmeRate_of fmrTrainClose UnforcedLeray.Short.IIb.cylClassicalExists _root_.cylWeakEqClassical
    fmrRegular fmrTransfer

end UnforcedLeray.Short.IIIa
