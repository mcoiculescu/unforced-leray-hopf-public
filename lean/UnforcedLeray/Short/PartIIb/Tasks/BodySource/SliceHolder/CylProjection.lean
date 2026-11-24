import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2_loc
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvWeakLeibniz
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.P0SliceLiftH1

namespace UnforcedLeray.Short.IIb

/-!

-/

theorem cylBodySourceProjection_proof :
    UnforcedLeray.Short.IIb.CylBodySourceProjection :=
  cylBodySourceProjection_of_leaves_loc
    flatBvWeakLeibniz_proof
    flatBvSliceGoodAe_proof
    p0SliceLiftH1Loc_proof

end UnforcedLeray.Short.IIb
