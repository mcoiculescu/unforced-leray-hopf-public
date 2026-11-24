import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.AgeRange
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.PhysClassical
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.MovingSubst
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.Rescale
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.InteractionUnique

/-!
# Part III-a, `PartIII-a:T21/2/2/2/1`: `MovingAdjointEq m` for `8 < m`

Assembles `movingAdjointEq_of` from the four compiled leaves (`adjRangeAge`,
`physAdjClassical`, `movingSubstitution`, `interactionRescale`, `interactionUnique`).
Source: `the November 2 reference manuscript`, lines 2854-2865 and 3052-3060.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.E0

/-- `MovingAdjointEq m` for `8 < m`, from the four leaves. -/
theorem movingAdjointEq (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.E0.MovingAdjointEq m :=
  movingAdjointEq_of m adjRangeAge (physAdjClassical m hm) (movingSubstitution m)
    interactionRescale interactionUnique

end UnforcedLeray.Short.IIIa.E0
