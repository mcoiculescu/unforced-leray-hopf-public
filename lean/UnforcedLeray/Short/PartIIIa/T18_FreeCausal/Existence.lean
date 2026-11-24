import UnforcedLeray.Short.PartIIIa.Sub.T18_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceApprox
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NullModification

/-!
# Part III-a, task `PartIII-a:T18/2`: existence for the free causal solver (unconditional assembly)

Target (`Sub/T18.lean`): `FreeCausalExistence`. The conditional theorem `freeCausalExistence_of`
(`Sub/T18_2.lean`) takes the six ingredients as hypotheses; each is supplied here by its
unconditional theorem:

* `causalSolSub` (`T18_FreeCausal/Lin.lean`, task `T18/1`),
* `freeCausalEnergyBound` (`T18_FreeCausal/EnergyBound.lean`, task `T18/3`),
* `niceForceApprox` (`T18_FreeCausal/Existence/NiceForceApprox.lean`),
* `niceForceSolution` (`T18_FreeCausal/Existence/NiceForceSolution.lean`),
* `causalLimitAE` (`T18_FreeCausal/Existence/CausalLimitAE.lean`),
* `causalNullModification` (`T18_FreeCausal/Existence/NullModification.lean`).

Source of record: `the November 2 reference manuscript`, lines 3427-3440.
-/

namespace UnforcedLeray.Short.IIIa

theorem freeCausalExistence : UnforcedLeray.Short.IIIa.FreeCausalExistence :=
  freeCausalExistence_of causalSolSub freeCausalEnergyBound niceForceApprox niceForceSolution
    causalLimitAE causalNullModification

end UnforcedLeray.Short.IIIa
