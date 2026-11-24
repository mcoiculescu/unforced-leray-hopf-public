import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import UnforcedLeray.Lib.Axisymmetric.Measure
import UnforcedLeray.Lib.Axisymmetric.RingChart
import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import UnforcedLeray.Lib.Axisymmetric.Laplacian
import UnforcedLeray.Lib.Axisymmetric.PhysicalChart
import UnforcedLeray.Lib.Axisymmetric.Tensor

/-!
# Wave 1, block 1E part 2: axisymmetric calculus (INF23 targets AX01–AX03, AX08 `phase_shift`)


block 1E CYL0, INF23 part) and scoping note `scoping/INF13-INF23-Cylinder.md` (§5, Layer 3).
Critic correction 3 (`scoping/critic.md`) keeps only `phase_shift` of AX08 in Wave 1.
Namespace `UnforcedLeray.Axi`; physical space is `UnforcedLeray.Space`.

* AX01 (`Axisymmetric/Cylindrical.lean`): `ϱ`, `axis`, `eR`, `eΦ`, `liftMer`,
  `isAxisymmetricNoSwirl_liftMer`, `contDiffOn_liftMer`, `hasFDerivAt_liftMer`,
  `divergence_liftMer`, `curl_liftMer`, `advection_liftMer`, `norm_liftMer`;
  second order (`Axisymmetric/Laplacian.lean`): `lap_comp_mer`, `lap_mul`, `vecLap_liftMer`;
  tensors (`Axisymmetric/Tensor.lean`): `liftTensor`, `IsMeridTensor`, `frobenius_liftTensor`.
* AX02 (`Axisymmetric/Measure.lean`): `lintegral_cylindrical`, `lintegral_axisymm`,
  `volume_axis`.
* AX03 (`Axisymmetric/RingChart.lean`, `Axisymmetric/RingMeasure.lean`): `age`, `phase`,
  `trans`, `chart`, `lintegral_ringChart`, `phaseAvg_ringChart`, `radial_chain`,
  `axial_chain`, `phase_chain`, `T0_chain`.
  Bridge to the audited physical chart `RingLift.Chart` (B0184): `chart_similarity`
  (`Axisymmetric/PhysicalChart.lean`).
* AX08 (part): `phase_shift`, `chart_add_period` (in `Axisymmetric/RingChart.lean`).

Not built here: the rest of AX08 (`Nv_dss`, `physical_dss`), which needs AX04 (Wave 2J).

Blueprint units: B0184–B0187, B0197, B0219, B0222, B0226, B0443, B0483, B0485, B0550, B0782.
-/
