import UnforcedLeray.Short.PartIIb.Sub.T15
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.SPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.QDecomposition

/-!
# Part II-b, task `PartII-b:T15` assembly: the Hilbert energy tools

Assembles the three leaves `weakSPeriodicExtension` (`PartII-b:T15/1`), `weakProductRuleH2`
(`PartII-b:T15/2`) and `weakQDecomposition` (`PartII-b:T15/3`) into the conditional theorem
`hilbertEnergy_of` of `Sub/T15.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **`drift_identity_H2`** (SP 1975-1979): the drift identity, first component of `hilbertEnergy_of`. -/
theorem drift_identity_H2 : UnforcedLeray.Short.IIb.DriftIdentityH2 :=
  (hilbertEnergy_of weakSPeriodicExtension weakProductRuleH2 weakQDecomposition).1

/-- **`diffusion_difference_terms`** (SP 1960-1966): the two-term diffusion difference, second
component of `hilbertEnergy_of`. -/
theorem diffusion_difference_terms : UnforcedLeray.Short.IIb.DiffusionDifferenceTerms :=
  (hilbertEnergy_of weakSPeriodicExtension weakProductRuleH2 weakQDecomposition).2

end UnforcedLeray.Short.IIb
