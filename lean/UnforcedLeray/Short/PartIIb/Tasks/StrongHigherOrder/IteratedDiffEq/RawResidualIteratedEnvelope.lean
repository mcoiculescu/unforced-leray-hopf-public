import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1_2
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.EarlyJetAll
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope.LateTail

/-!
# `PartII-b:S2/1/2`: `RawResidualIteratedEnvelope`

Source of record: `the November 2 reference manuscript`, lines 1206-1222,
2542-2551, 2563-2569.

Assembles `rawResidualIteratedEnvelope_proof` from `rawResidualIteratedEnvelope_of`,
`resProfileEarlyJetAll_proof`, and `rawResidualIteratedLateTail_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem rawResidualIteratedEnvelope_proof : UnforcedLeray.Short.IIb.RawResidualIteratedEnvelope :=
  rawResidualIteratedEnvelope_of resProfileEarlyJetAll_proof _root_.rawResidualIteratedLateTail_proof

end UnforcedLeray.Short.IIb
