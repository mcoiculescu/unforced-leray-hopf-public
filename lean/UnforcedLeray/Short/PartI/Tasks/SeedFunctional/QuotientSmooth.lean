import UnforcedLeray.Short.PartI.Sub.PartI_S09_2
import UnforcedLeray.Short.PartI.Tasks.SeedFunctional.GreenTwoSmooth

/-!
# Part I, task `PartI:S09/2` (`SeedQuotientSmooth`): proof

Source: `the November 2 reference manuscript`
lines 606-609 ("The quotients at `k = 0` are removable").

Reduction `seedQuotientSmooth_of` (in `Sub/PartI_S09_2`) to the leaf `GreenTwoSmooth`,
which is proved in `Tasks/SeedFunctional/GreenTwoSmooth` as `greenTwoSmooth_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem seedQuotientSmooth_proof : UnforcedLeray.Short.PartI.SeedQuotientSmooth :=
  seedQuotientSmooth_of greenTwoSmooth_proof

end UnforcedLeray.Short.PartI
