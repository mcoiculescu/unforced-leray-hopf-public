import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_B
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_D

/-!
# `freeWeakUniqueness`: free weak uniqueness from the four sub-lemmas

Source: `the November 2 reference manuscript` lines 1580-1583 (subtraction of two
solutions), 1351-1362 (`bg:common-body-graph`), 2666-2700 (lift of `VelG` into `Y_2`).
`freeWeakUniqueness_of` (Sub file `PartIIIb-D2_1`) reduces the statement to the sub-lemmas
`FWUSub` (`fwuSub`, file `_A`), `FWULiftYr` (`fwuLiftYr`, file `_B`), `FWUHomog` (`fwuHomog`,
file `_C`) and `FWULiftInj` (`fwuLiftInj`, file `_D`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem freeWeakUniqueness {c γ ν ε μ : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hP : 2 * ε * c ≤ 1) (hμ : 0 < μ + 1 / 4) : FreeWeakUniqueness c γ ν ε μ :=
  freeWeakUniqueness_of hc hν hε hP hμ (fwuSub hc hν hε) (fwuLiftYr hc hν hε) fwuHomog
    (fwuLiftInj hc hν hε)

end UnforcedLeray.Short.PartIIIb.Concrete
