import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.SolCurlFree
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelWeakDeriv

/-!
# `BSSol` from the Fubini swap alone

Source `the November 2 reference manuscript` lines 1351-1362 (`div ψ = 0` for the
Coulomb-gauge stream potential `ψ = bsPot Φ`).  `bsSol_of'` (`SolCurlFree.lean`) with the accepted
`bsSliceL2` and `bsKernelWeakDeriv`; the only remaining input is `BSFubiniSwap`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsSol_of_swap (hSw : BSFubiniSwap) : BSSol :=
  bsSol_of' hSw bsSliceL2 bsKernelWeakDeriv

end UnforcedLeray.Short.PartIIIb.Concrete
