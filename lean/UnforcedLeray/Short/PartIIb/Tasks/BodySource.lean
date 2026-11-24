import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder

/-!
# Part II-b, task `PartII-b:F5`: the body source bound `short-bg:source`

Source of record: `the November 2 reference manuscript` (SP), lines 2211-2246,
display `short-bg:source` at line 2237.

Definitions (`mulS`, `flatBv`, `IsBodySource`, `profCurl`, `sliceLpNorm`, `sliceH1Norm`,
`sliceXmNorm`, `sLpNorm`, `BodySourceBound`, `FlatGraphD2Slice`, `BodySourceSliceHolder`) and the
conditional assembly `bodySourceBound_of` live in `Short/PartII-b/Sub/PartII-b_F5.lean`.
Once the leaves `PartII-b:F5/1` (`flatGraphD2Slice_proof`) and `PartII-b:F5/2`
(`bodySourceSliceHolder_proof`) are proved, assemble `bodySourceBound_proof : BodySourceBound` here.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem bodySourceBound_proof : UnforcedLeray.Short.IIb.BodySourceBound :=
  bodySourceBound_of flatGraphD2Slice_proof bodySourceSliceHolder_proof

end UnforcedLeray.Short.IIb
