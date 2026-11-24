import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjSolve
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjDensity

/-!
# `PartIII-b:IIIb-D2/1/3/1`: `fwuDense`

Assembly of the two lemmas `fwuAdjSolve` (`AdjSolve.lean`, `PartIII-b:IIIb-D2/1/3/1/1`) and
`fwuAdjDensity` (`AdjDensity.lean`, `PartIII-b:IIIb-D2/1/3/1/2`) through `fwuDense_of`
(`Sub/PartIII-b_IIIb-D2_1_3_1.lean`).
Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fwuDense : FWUDense :=
  fwuDense_of fwuAdjSolve fwuAdjDensity

end UnforcedLeray.Short.PartIIIb.Concrete
