import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_4
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelFree
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelCollective
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelNorm

/-!
# `PartII-b:F2/4` (`CompactDuhamelBlock.lean`): Compact-Duhamel block approximation

Source of record: `the November 2 reference manuscript` (SP), lines 841–852,
931–953, 2104–2115, 2145–2166 (`short-bg:compact-duhamel`).

Assembles `compactDuhamelBlockStep_proof` from `compactDuhamelBlockStep_of`,
`freeTransportComparison_proof`, `planarDuhamelCollectiveCompact_proof`, and
`compactDuhamelNormConvergence_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem compactDuhamelBlockStep_proof : UnforcedLeray.Short.IIb.CompactDuhamelBlockStep :=
  compactDuhamelBlockStep_of
    _root_.freeTransportComparison_proof
    _root_.planarDuhamelCollectiveCompact_proof
    _root_.compactDuhamelNormConvergence_proof

end UnforcedLeray.Short.IIb
