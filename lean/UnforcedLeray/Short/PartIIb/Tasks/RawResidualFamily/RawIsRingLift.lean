import UnforcedLeray.Short.PartIIb.Sub.R1_5
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Part II-b, task `PartII-b:R1/5`: unconditional form of `RawIsRingLift`

Source of record: `the November 2 reference manuscript`, Proposition `sct:lift`
(lines 1203-1250) and eq. `m3-ring-lift` (line 2040-2046).  The conditional theorem
`rawIsRingLift_of` (`Sub/R1_5.lean`) takes `PartI.TrainStreamSmooth` as input; that input is
supplied unconditionally by `PartI.trainStreamSmooth` (task `PartI:T01/1`).
-/

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:R1/5`.** Unconditional form of `RawIsRingLift` (lines 1203-1250, 2040-2046). -/
theorem rawIsRingLift_proof : UnforcedLeray.Short.IIb.RawIsRingLift :=
  rawIsRingLift_of UnforcedLeray.Short.PartI.trainStreamSmooth

end UnforcedLeray.Short.IIb
