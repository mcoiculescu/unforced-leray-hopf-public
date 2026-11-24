import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_4_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.PerGauss

/-!
# Part II-b, task `PartII-b:T12/7/4/4` (`DeqhpGaussInt`): the Gaussian integrability statement

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`DeqhpGaussInt` is discharged by the decomposition `deqhpGaussInt_of`, which reduces it to the
single leaf `DeqhpPerGauss`; the leaf is proved in `HeatPair/PerGauss.lean` as `deqhpPerGauss`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem deqhpGaussInt : DeqhpGaussInt := deqhpGaussInt_of deqhpPerGauss

end UnforcedLeray.Short.IIb
