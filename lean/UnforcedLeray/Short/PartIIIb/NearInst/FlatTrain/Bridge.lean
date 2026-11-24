import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Defs

/-!
# The flat train multiplier bound is the BUC form (source 270-288, 2040, 2714-2729)

Source of record: `the November 2 reference manuscript`.

`FlatTrainMultBound` (`NearInst/Targets.lean`) carries the class hypothesis
`PartI.IsBUCTrain tr` of the train of Proposition `sct:train` (source 270-288, 2040), so it is
`FlatTrainMultBoundBUC` (`NearInst/FlatTrain/Defs.lean`) verbatim.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- `FlatTrainMultBound` is `FlatTrainMultBoundBUC` (the same statement, source 2714-2729 for the
BUC train of `sct:train`, 270-288, 2040). -/
theorem flatTrainMultBound_iff_buc : FlatTrainMultBound ↔ FlatTrainMultBoundBUC := Iff.rfl

end UnforcedLeray.Short.PartIIIb.NearInst
