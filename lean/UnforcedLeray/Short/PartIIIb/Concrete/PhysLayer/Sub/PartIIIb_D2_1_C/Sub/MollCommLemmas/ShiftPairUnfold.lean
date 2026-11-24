import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftPairUnfold.Tiling
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftPairUnfold.CellSum
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.ShiftPairUnfold.Subst

/-!
# `ShiftPairUnfold` from the three source facts

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
The three facts `ShiftPairTiling`, `ShiftPairCellSum`, `ShiftPairSubst` are proved in
`ShiftPairUnfold/{Tiling,CellSum,Subst}.lean`; `shiftPairUnfold_of` combines them into
`ShiftPairUnfold`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem shiftPairUnfold : ShiftPairUnfold :=
  shiftPairUnfold_of shiftPairTiling shiftPairCellSum shiftPairSubst

end UnforcedLeray.Short.PartIIIb.Concrete
