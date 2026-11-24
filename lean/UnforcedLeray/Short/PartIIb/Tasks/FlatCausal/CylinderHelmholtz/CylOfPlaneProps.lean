import UnforcedLeray.Short.PartIIb.Sub.T12_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.Unfold
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.AEMeas
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.PairingIntegrable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.CutoffTests
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.StreamDecomp
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.CellAverage
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.DerivZeroLr

/-!


Target `cylOfPlaneProps : CylOfPlaneProps` (definition in `Sub/T12_1.lean`, line 163). Source of
record: `the November 2 reference manuscript`, line 1670 (the ordinary planar
cylinder projection `P_0`) and lines 1727-1731 (the zero-frequency remark).

The proof is the conditional theorem `cylOfPlaneProps_of` (`Sub/T12_1_5.lean`, line 422) applied to
the nine leaf results, one per hypothesis:

* `cylUnfold` (`CylOfPlaneProps/Unfold.lean`): unfolding against a compactly supported weight.
* `cylLpAEMeas` (`CylOfPlaneProps/AEMeas.lean`): `L^r` periodic fields are a.e.-strongly measurable.
* `cylPairingIntegrableOn` (`CylOfPlaneProps/PairingIntegrable.lean`): integrability of the pairings.
* `cylCutoffTests` (`CylOfPlaneProps/CutoffTests.lean`): cutoff of a cylinder test is a planar test.
* `cylStreamDecomp` (`CylOfPlaneProps/StreamDecomp.lean`): stream-function decomposition of solenoidal
  tests (uses `SmoothPrimEta` and `CylFluxConst`, imported transitively).
* `cylCellAverage` (`CylOfPlaneProps/CellAverage.lean`): the `q`-average lies in `L^r(R)`.
* `oneDDerivZeroLr` (`CylOfPlaneProps/DerivZeroLr.lean`): a one-dimensional distribution with zero
  derivative in `L^r(R)`, `1 < r`, vanishes.

No new mathematics is proved in this file.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylOfPlaneProps : CylOfPlaneProps :=
  cylOfPlaneProps_of cylUnfold cylLpAEMeas cylPairingIntegrableOn cylCutoffTests cylStreamDecomp
    cylCellAverage oneDDerivZeroLr

end UnforcedLeray.Short.IIb
