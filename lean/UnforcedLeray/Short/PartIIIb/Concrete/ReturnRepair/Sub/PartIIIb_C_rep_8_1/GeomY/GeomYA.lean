import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.YoungAzi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.PhasePrimitive
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.TaylorWidth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.ZRegular
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.StreamCutAlg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.RayFTC

/-!
# `PartIII-b:C/rep/8/1/1/2/4` (`geomYA`): kernel comparison of `Y_A = 𝒞_y W_μ`

Source `the November 2 reference manuscript`
lines 5415-5432. Assembles `D.GeomYA` from `geomYA_of_leaves` and the proved leaves
`streamCutAlg`, `rayFTC`, `youngWRayAzi`, `phasePrimitiveYA`, `taylorWidthYA`, `zRegularYA`,
and `measYA`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/1/1/2/4`** (`geomYA`): kernel comparison of `Y_A = 𝒞_y W_μ` along the
sequence (source lines 5415-5432). -/
theorem geomYA (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.GeomYA :=
  geomYA_of_leaves D hst streamCutAlg rayFTC youngWRayAzi (phasePrimitiveYA D hst)
    (taylorWidthYA D hst) (zRegularYA D hst) (measYA D hst)

end UnforcedLeray.Short.PartIIIb.Concrete

end
