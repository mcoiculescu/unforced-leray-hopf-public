import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2_10
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakL2.ExistsVecH1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakL2.SobWeakOfPairing
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakL2.PairingOfSobWeak

/-!
# Part III-a, task `PartIII-a:T18/2/4/2/10`: `P0CommWeakL2`

Assembles the three packaging leaves (`P0CommWeakL2/`) into `P0CommWeakL2` through
`p0CommWeakL2_of` (`Sub/T18_2_4_2_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 3442-3465.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem p0CommWeakL2 : UnforcedLeray.Short.IIIa.P0CommWeakL2 :=
  p0CommWeakL2_of existsVecH1OfWeak sobWeakOfPairing pairingOfSobWeak

end UnforcedLeray.Short.IIIa
