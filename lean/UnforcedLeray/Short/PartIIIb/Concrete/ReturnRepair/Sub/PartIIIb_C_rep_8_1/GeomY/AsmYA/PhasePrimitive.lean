import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_1_1_2_4_1.Far
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeaf

/-!
# `PartIII-b:C/rep/8/1/1/2/4/1` (`phasePrimitiveYA`)

Source `the November 2 reference manuscript`
lines 5400-5427.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phasePrimitiveYA (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.PhasePrimitiveYA :=
  PhasePrimYA.phasePrimitiveYA_of_far sepOscFar D hst

end UnforcedLeray.Short.PartIIIb.Concrete

end
