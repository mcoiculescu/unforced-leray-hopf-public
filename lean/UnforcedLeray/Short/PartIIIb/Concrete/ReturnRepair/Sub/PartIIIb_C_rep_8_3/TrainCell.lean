import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.TrainSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_4.PartICell
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_4.GaussCell

/-!
# `PartIII-b:C/rep/8/3/2/4`: `TrainGaussCell` from Part I `sct:fixed-band`

Source `the November 2 reference manuscript` 5484-5492, Part I 468-478.
`trainGaussCell_of_leaves` (in `Sub/PartIII-b_C_rep_8_3_2_4.lean`) reduces `TrainGaussCell` to
`TrainPartICell` (leaf 1), `GaussCellFromPartI` (leaf 2) and `TrainSliceSmooth`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`TrainGaussCell` from `TrainFixedBand` and `TrainGaussPt`** (source 5484-5492,
Part I 468-478). -/
theorem trainGaussCell_of (hF : UnforcedLeray.Short.PartI.TrainFixedBand) (hP : TrainGaussPt) :
    TrainGaussCell :=
  trainGaussCell_of_leaves (fun hF => trainPartICell_of hF) gaussCellFromPartI trainSliceSmooth
    hF hP

end UnforcedLeray.Short.PartIIIb.Concrete

end
