import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.AdjFullEquationProof
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommFinal

/-!
# `MollCommutatorLimit`: leaf 4 assembly

Source `the November 2 reference manuscript` lines 1351-1362 and 1556-1583.
Assembles `mollCommutatorLimit` from the full adjoint equation `adjFullEquation`
(`AdjFullEquationProof.lean`) and the unconditional Friedrichs limit `mollCommutatorLimitFull`
(`MollCommFinal.lean`) via `mollCommutatorLimit_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollCommutatorLimit : MollCommutatorLimit :=
  mollCommutatorLimit_of adjFullEquation mollCommutatorLimitFull

end UnforcedLeray.Short.PartIIIb.Concrete
