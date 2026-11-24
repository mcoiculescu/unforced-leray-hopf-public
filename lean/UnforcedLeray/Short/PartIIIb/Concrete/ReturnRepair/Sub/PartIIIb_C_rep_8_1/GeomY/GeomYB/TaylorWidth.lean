import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.NewtonComm

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2`: assembly of `D.TaylorWidthYBBound`

Composition of `YBWidth.taylorWidthYBBound_of` (TaylorWidth/Of.lean) with the two leaves
`sepCommMeanFar` (TaylorWidth/SepComm.lean) and `newtonCommBridge` (TaylorWidth/NewtonComm.lean).
Source the November 2 reference manuscript 5427-5432, 5383-5387.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem taylorWidthYBBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.TaylorWidthYBBound :=
  YBWidth.taylorWidthYBBound_of YBWidth.sepCommMeanFar YBWidth.newtonCommBridge D hst

end UnforcedLeray.Short.PartIIIb.Concrete
