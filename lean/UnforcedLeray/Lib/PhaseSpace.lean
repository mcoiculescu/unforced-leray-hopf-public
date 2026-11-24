import UnforcedLeray.Lib.PhaseSpace.Test
import UnforcedLeray.Lib.PhaseSpace.Ops
import UnforcedLeray.Lib.PhaseSpace.Pairing
import UnforcedLeray.Lib.PhaseSpace.Graph
import UnforcedLeray.Lib.PhaseSpace.Multiplier
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc
import UnforcedLeray.Lib.PhaseSpace.PointSingularity
import UnforcedLeray.Lib.PhaseSpace.Cutoff
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest
import UnforcedLeray.Lib.PhaseSpace.Charts
import UnforcedLeray.Lib.PhaseSpace.Leibniz

/-!
# Block 1F PHASE0: the phase space `Y_q`, its distributional graphs and charts


INF25 T25.1–T25.3, T25.5, T25.7, T25.12 of the scoping note `INF15-INF17-INF25-Parabolic.md`
§5. Blueprint units served: B0005 (tex 136–147), B0411 (7304–7337), B0412 (5085–5091),
B0413 (5750–5753), B0427 (7540–7542), B0447 (7633–7662), B0687 (5855–5865).

* `Test`, `Ops`, `Pairing` (T25.1): `Yq` (decision D2), `IsPhaseTest`, transposed operators,
  `phasePair` and its period-integral formula.
* `Graph` (T25.2): `HasPhaseOp`, `freeGraph`, `solenoidalFreeGraph`, closedness, completeness.
* `ExtendedTest` with `Multiplier`, `CutoffCalc`, `Cutoff` (T25.3): `IsPhaseSchwartz`,
  `HasPhaseOp.extend_dy`, `extend_lap`, `extend_drift`, `freeGraph_extend`.
* `Charts` (T25.5, norm half): `comovingChart`, `chartPullback`, `stripNorm`, `chart_norm_le`.
* `PointSingularity` (T25.7): `isSolenoidal_of_punctured`.
* `Leibniz` (T25.12, commutator): `dy_driftT`, `dy_lapT`, `freeGraph_commutator_deriv`.

Status: infrastructure. No unit is proved in full here, and Theorem A is not proved in Lean.
-/
