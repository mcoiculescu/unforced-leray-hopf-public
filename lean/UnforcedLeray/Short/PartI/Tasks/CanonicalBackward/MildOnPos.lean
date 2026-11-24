import UnforcedLeray.Short.PartI.Sub.PartI_C08_1
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.MildOnPosContinuous
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.MildOnPosFullMildEq
import UnforcedLeray.Short.PartI.Tasks.CanonicalBackward.FullMildImpliesCoupled

/-!
# `PartI:C08/1`: proof of `MildOnPosImpliesCanonicalMild`

Source `the November 2 reference manuscript`,
lines 1094-1125.  The three leaf proofs are composed through `mildOnPosImpliesCanonicalMild_of`
(`Sub/PartI_C08_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open UnforcedLeray Set

theorem mildOnPosImpliesCanonicalMild_proof : UnforcedLeray.Short.PartI.MildOnPosImpliesCanonicalMild :=
  mildOnPosImpliesCanonicalMild_of mildOnPosContinuous_proof mildOnPosFullMildEq_proof
    fullMildImpliesCoupled_proof

end UnforcedLeray.Short.PartI
