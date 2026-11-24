import UnforcedLeray.Short.PartIIb.Sub.G4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSource
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSup

/-!
# Part II-b, task `PartII-b:G4`: `AffineInletFacts`

Assembles `affineInletFacts_proof : AffineInletFacts` from `affineInletFacts_of` and the leaf
theorems `affineColumnComparison`, `_root_.inletSourceBound`, `inletSupBound`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem affineInletFacts_proof : UnforcedLeray.Short.IIb.AffineInletFacts :=
  affineInletFacts_of affineColumnComparison _root_.inletSourceBound inletSupBound

end UnforcedLeray.Short.IIb
