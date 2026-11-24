import UnforcedLeray.Short.PartI.Sub.PartI_S09
import UnforcedLeray.Short.PartI.Tasks.SeedFunctional.AdjPairing
import UnforcedLeray.Short.PartI.Tasks.SeedFunctional.QuotientSmooth

/-!
# Part I, task `PartI:S09` (`SeedFunctional`): assembly

Source: `the November 2 reference manuscript` lines 603-609 and 890-912.
The two leaves `PartI:S09/1` (`seedAdjPairing_proof`) and `PartI:S09/2`
(`seedQuotientSmooth_proof`) are combined by `seedFunctional_of` from `Sub/PartI_S09`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem seedFunctional_proof : SeedFunctional :=
  seedFunctional_of seedAdjPairing_proof seedQuotientSmooth_proof

end UnforcedLeray.Short.PartI
