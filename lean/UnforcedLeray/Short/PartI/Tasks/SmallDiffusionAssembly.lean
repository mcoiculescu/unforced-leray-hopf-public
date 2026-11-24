import UnforcedLeray.Short.PartI.Sub.PartI_C05
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildExists
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildCocycle
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildShortBound
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.FreeLimitExp

/-!
# Part I, task `PartI:C05`: assembly of `SmallDiffusionComplement`

Source of record: `the November 2 reference manuscript`, lines 1005-1058.
The five leaf lemmas are proved in the sibling files of this folder; this file only composes them
through `smallDiffusionComplement_of` from `Sub/PartI_C05.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem smallDiffusionComplement_proof : SmallDiffusionComplement :=
  smallDiffusionComplement_of mildComplementExists mildComplementCocycle
    mildComplementShortBound mildComplementInvariant freeLimitExpBound

end UnforcedLeray.Short.PartI
