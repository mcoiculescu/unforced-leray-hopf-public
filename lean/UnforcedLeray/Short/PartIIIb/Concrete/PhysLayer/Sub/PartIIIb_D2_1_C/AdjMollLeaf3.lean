import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollMinkowskiProof
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PhaseTranslateContinuousProof

/-!
# `MollApproxIdentity`: leaf 3 assembly

Source `the November 2 reference manuscript` lines 1556-1583.
Assembles `mollApproxIdentity_of` from `mollMinkowski` (Minkowski's integral inequality in the
cell) and `phaseTranslateContinuous` (continuity of translation in the cell `L²` norm).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollApproxIdentity : MollApproxIdentity :=
  mollApproxIdentity_of mollMinkowski phaseTranslateContinuous

end UnforcedLeray.Short.PartIIIb.Concrete
