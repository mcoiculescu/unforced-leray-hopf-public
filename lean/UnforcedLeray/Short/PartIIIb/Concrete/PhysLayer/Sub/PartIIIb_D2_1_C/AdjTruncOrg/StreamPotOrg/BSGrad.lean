import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGradOrg.Of
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSGradOrg.Vec
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsFubiniSwap

/-!
# `BSGrad`: the Biot-Savart potential has a weak `y`-gradient in `Y_2`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362.

`Dψ j` is the `Y_2` representative of `τ ↦ bsGradL2 j (Φ(τ))`, where
`bsGradL2 j f = ∑_{c,b} R_{jc}(f_b) (e_c × e_b)` is the slice gradient (`BSGradOrg/Defs.lean`,
`R_{jc} = rieszPairL2 j c`).  Assembly `bsGrad_of'` (`BSGradOrg/Of.lean`) from the Fubini swap
`bsFubiniSwap`, the kernel identity `bsgKernelVec` and the duality `bsgDualVec`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsGrad : BSGrad := bsGrad_of' bsFubiniSwap bsgKernelVec bsgDualVec

end UnforcedLeray.Short.PartIIIb.Concrete
