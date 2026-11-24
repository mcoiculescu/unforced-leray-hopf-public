import UnforcedLeray.Short.PartIIIa.Sub.TrainClassIIIa.Bridges
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrVelImage
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrVelCompSup
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof

/-!
# `PartIII-a:T21/c2/2/7`: `FmrVelGap`

Source `the November 2 reference manuscript` lines 2955, 291-303, 270-288.
Assembled by `fmrVelGap_of_parts` (`Sub/TrainClassIIIa/Bridges.lean`) from `fmrVelImage`,
`fmrVelCompSup`, and `PartI.trainComparison_proof` (task `PartI:T10`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem fmrVelGap : FmrVelGap :=
  fmrVelGap_of_parts fmrVelImage fmrVelCompSup UnforcedLeray.Short.PartI.trainComparison_proof

end UnforcedLeray.Short.IIIa
