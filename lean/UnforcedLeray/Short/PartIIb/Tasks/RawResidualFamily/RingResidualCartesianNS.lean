import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.SimT0Scaling
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.SimLapScaling
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.SimAdvScaling
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.SimGradScaling
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.CylTimeFormula
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.CylAdvFormula
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.CylLapFormula
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.CylGradFormula
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.LiftMeridSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.CylFieldSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.TrainPressureSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Part II-b, task `PartII-b:R1/7`: assembly of `RingResidualCartesianNS`

Source of record: `the November 2 reference manuscript`, Proposition `sct:lift`
(lines 1203-1263; `F_R = s^{3/2} r` at line 1263) and lines 261-288 (the BUC train is smooth for
positive time).  No new mathematics: the eleven accepted leaves are assembled by
`ringResidualCartesianNS_of` (`Sub/R1_7.lean`), with the stream-smoothness input supplied by
`trainStreamSmoothBUC_of` from the unconditional `PartI.trainStreamSmooth` (task `PartI:T01/1`).
-/

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:R1/7`.** Assembly of `RingResidualCartesianNS` (lines 1203-1263, 261-288). -/
theorem ringResidualCartesianNS_proof : UnforcedLeray.Short.IIb.RingResidualCartesianNS :=
  ringResidualCartesianNS_of simT0Scaling simLapScaling simAdvScaling simGradScaling
    cylTimeFormula cylAdvFormula cylLapFormula cylGradFormula liftMeridSmooth cylFieldSmooth
    trainPressureSmooth
    (trainStreamSmoothBUC_of UnforcedLeray.Short.PartI.trainStreamSmooth)

end UnforcedLeray.Short.IIb
