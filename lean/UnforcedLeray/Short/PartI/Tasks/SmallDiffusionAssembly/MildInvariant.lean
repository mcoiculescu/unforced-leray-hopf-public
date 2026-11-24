import UnforcedLeray.Short.PartI.Sub.PartI_C05_4
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.PairingIdentity

/-!
# Target `PartI:C05/4`: invariance of `ker ℓ` under the mild complementary evolution

Source of record: `the November 2 reference manuscript`, lines 1056-1058
("testing the mild equation against `q†` in `dom D`"). The scalar pairing identity
`MildPairingIdentity` (target `PartI:C05/4/3`) is proved in `MildInvariant/PairingIdentity.lean`,
and `mildComplementInvariant_of` turns it into `MildComplementInvariant` by the scalar ODE argument.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target `PartI:C05/4`**: invariance of `ker ℓ` under the mild complementary evolution. -/
theorem mildComplementInvariant : MildComplementInvariant :=
  mildComplementInvariant_of mildPairingIdentity

end UnforcedLeray.Short.PartI
