import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.SolOfSwap
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsFubiniSwap

/-!
# `BSSol`: the Coulomb-gauge stream potential is divergence free

Source `the November 2 reference manuscript` lines 1351-1362 (`div ψ = 0` for
`ψ = bsPot Φ`), with `Y_2` input from lines 1334-1337.

Assembly `bsSol_of_swap` (`Fubini/SolOfSwap.lean`) applied to the accepted Fubini swap
`bsFubiniSwap` (`Fubini/BsFubiniSwap.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsSol : BSSol := bsSol_of_swap bsFubiniSwap

end UnforcedLeray.Short.PartIIIb.Concrete
