import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.TrainLp22over3
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.TrainLp22over3Loc
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection

/-!
# Part II-b, task `PartII-b:F5/2`: slice-level `L^{22/3}`–`L^{11/4}` Hölder and body source assembly

Decomposed into `Short/PartII-b/Sub/PartII-b_F5_2.lean`:
* `PartII-b:F5/2/1` (`TrainWeightedLp22over3` in `Tasks/BodySource/SliceHolder/TrainLp22over3.lean`);
* `PartII-b:F5/2/2` (`CylBodySourceProjection` in `Tasks/BodySource/SliceHolder/CylProjection.lean`);
* conditional assembly `UnforcedLeray.Short.IIb.bodySourceSliceHolder_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bodySourceSliceHolder_proof : UnforcedLeray.Short.IIb.BodySourceSliceHolder :=
  bodySourceSliceHolder_of
    trainWeightedLp22over3_proof
    trainWeightedLp22over3Loc_proof
    cylBodySourceProjection_proof

end UnforcedLeray.Short.IIb

end
