import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopExists
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.PhysKopYoungLateBounds
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds.FlatK0opYoungLateBounds

/-!
# Part II-b, task `PartII-b:G2`: Young and late operator bounds (`YoungLateOperatorBounds`, SP 2432–2445)

Source of record: `the November 2 reference manuscript`
(SP), lines 2432–2445.

This file assembles `youngLateOperatorBounds_of` from `youngLateOperatorBounds_of_sub` and the
three proved leaf tasks `PartII-b:G2/1` (`physKopExists_proof`), `PartII-b:G2/2`
(`physKopYoungLateBounds_proof`), and `PartII-b:G2/3` (`flatK0opYoungLateBounds_proof`).
-/

namespace UnforcedLeray.Short.IIb

theorem youngLateOperatorBounds_of
    (h1 : UnforcedLeray.Short.IIb.StrongLateCoeff) :
    UnforcedLeray.Short.IIb.YoungLateOperatorBounds :=
  youngLateOperatorBounds_of_sub
    physKopExists_proof
    _root_.physKopYoungLateBounds_proof
    _root_.flatK0opYoungLateBounds_proof
    h1

end UnforcedLeray.Short.IIb
