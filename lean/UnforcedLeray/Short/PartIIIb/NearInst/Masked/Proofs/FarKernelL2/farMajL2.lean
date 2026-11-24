import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2.Minkowski
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2.SliceMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2.SliceL2

/-!


Composes the three steps `minkowskiL2` (Minkowski in `L²`), `farSliceMeasurable` (joint
measurability of the slices) and `farSliceL2` (slice `L²` bound) through `farMajL2_of`.
-/

set_option autoImplicit false

noncomputable section

theorem farMajL2 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.FarMajL2 :=
  UnforcedLeray.Short.PartIIIb.NearInst.Masked.farMajL2_of
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.minkowskiL2
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.farSliceMeasurable
    farSliceL2

end
