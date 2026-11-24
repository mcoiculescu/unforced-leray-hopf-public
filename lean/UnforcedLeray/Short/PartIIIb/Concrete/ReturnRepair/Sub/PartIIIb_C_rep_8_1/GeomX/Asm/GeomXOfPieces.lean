import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.DPhaseMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.StreamCutAlg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.RayFTC

/-!
# `PartIII-b:C/rep/8/1/1/1/asm`: `GeomX` from the pieces

Source `the November 2 reference manuscript`
lines 4178-4186, 5415-5427. The assembly `GeomXAsm.geomX_of_leaves` takes the two calculus
statements and the measurability fact as hypotheses; here they are supplied by the proved leaves
`streamCutAlg`, `rayFTC` and `dPhaseMeas_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`GeomX` from the pieces** (source 4178-4186, 5415-5427): the stream-cut assembly with the
calculus leaves `streamCutAlg`, `rayFTC` and the measurability `dPhaseMeas_of` filled in. -/
theorem geomX_of_pieces (D : SeqData) (hχ : IsStreamCutoff D.K.χy)
    (hν : ∀ᶠ n : ℕ in Filter.atTop, (D.level n).ν ≤ 1) (hP : D.PhasePrimitive)
    (hT : D.TaylorWidth) (hR : D.ZRegular) (hZ : D.ZPrimRegular) (hS : StreamCutEq)
    (hM : D.XcmpCellMeas) : D.GeomX :=
  GeomXAsm.geomX_of_leaves D hχ hν streamCutAlg rayFTC hS hP hT hR hZ (dPhaseMeas_of D hR) hM

end UnforcedLeray.Short.PartIIIb.Concrete
