import UnforcedLeray.Short.PartIIIa.Sub.T18_2_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.TCalNormTriangle
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceApprox.Truncation
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceApprox.WeightCompare
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceApprox.SmoothDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceApprox.Periodize

/-!
# Part III-a, task `PartIII-a:T18/2/3`: density of nice forces (unconditional assembly)

Target (`Sub/T18_2.lean`): `NiceForceApprox`. Source of record:
`the November 2 reference manuscript`, lines 3427-3440 ("let `δ → 0`").

The target is assembled from the five leaf statements, each proved in its own module:

* `tCalNormTriangle : TCalNormTriangle` (`T18_FreeCausal/Existence/TCalNormTriangle.lean`);
* `niceTruncation : NiceTruncation` (`Existence/NiceForceApprox/Truncation.lean`);
* `niceWeightCompare : NiceWeightCompare` (`Existence/NiceForceApprox/WeightCompare.lean`);
* `niceSmoothDensity : NiceSmoothDensity` (`Existence/NiceForceApprox/SmoothDensity.lean`);
* `nicePeriodize : NicePeriodize` (`Existence/NiceForceApprox/Periodize.lean`);

and the two wiring lemmas `niceBoxApprox_of` and `niceForceApprox_of` of `Sub/T18_2_3.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **Density of nice forces** (`PartIII-a:T18/2/3`; SP 3427-3440). Unconditional: the wiring
`niceForceApprox_of` applied to the five proved leaves. -/
theorem niceForceApprox : UnforcedLeray.Short.IIIa.NiceForceApprox :=
  niceForceApprox_of tCalNormTriangle niceTruncation
    (niceBoxApprox_of niceWeightCompare niceSmoothDensity nicePeriodize)

end UnforcedLeray.Short.IIIa
