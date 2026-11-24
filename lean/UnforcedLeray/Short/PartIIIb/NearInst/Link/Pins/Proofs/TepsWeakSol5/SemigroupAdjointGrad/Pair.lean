import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair.Rep
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair.Good
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair.Fubini
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair.Scale
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Pair.Core

/-!
# `AdjPair` (task `PartIII-b:C/near/pins/3/5/4/4`)

Source `the November 2 reference manuscript`:
1339-1362, 3346-3352.

Assembly of the five leaves: `AdjPairRep` (representative formula), `RepXGood`
(measurability, periodicity, `L²` on one period), and `AdjPairCore`, which is obtained from
`AdjSpatial` (`adjSpatial_of` of the Fubini leaf `AdjSpatialFubini` and the scaling leaf
`AdjSpatialScale`) by the phase assembly `adjPairCore_of_spatial`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem adjPair : AdjPair :=
  adjPair_of adjPairRep repXGood (adjPairCore_of_spatial (adjSpatial_of adjSpatialFubini adjSpatialScale))

end UnforcedLeray.Short.PartIIIb.NearInst
