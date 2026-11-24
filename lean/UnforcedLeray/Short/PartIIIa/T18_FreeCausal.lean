import UnforcedLeray.Short.PartIIIa.Sub.T18
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound

/-!
# Part III-a, task `PartIII-a:T18`: the free causal solver (unconditional assembly)

Target: `FreeCausalExistsUnique` (`FlatCausal.lean`). The conditional theorem
`freeCausalExistsUnique_of` (`Sub/T18.lean`) takes `CausalSolSub`, `FreeCausalExistence` and
`FreeCausalEnergyBound` as hypotheses; each is supplied by its unconditional theorem:

* `causalSolSub` (`T18_FreeCausal/Lin.lean`, task `T18/1`),
* `freeCausalExistence` (`T18_FreeCausal/Existence.lean`, task `T18/2`),
* `freeCausalEnergyBound` (`T18_FreeCausal/EnergyBound.lean`, task `T18/3`).

Source of record: `the November 2 reference manuscript`, lines 3427-3440 and
3541-3552.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem freeCausalExistsUnique : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique :=
  freeCausalExistsUnique_of causalSolSub freeCausalExistence freeCausalEnergyBound

end UnforcedLeray.Short.IIIa
