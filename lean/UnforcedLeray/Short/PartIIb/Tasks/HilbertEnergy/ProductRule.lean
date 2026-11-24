import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.ExpChartIntegral
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogUMemLp
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestOfOrig
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogWeakTransfer
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogProductRule

/-!
# Part II-b, task `PartII-b:T15/2`: the weak product rule in the `H_2` measure

Assembly of the nineteen leaves through the conditional theorem `weakProductRuleH2_of`
(`Sub/T15_2.lean`). Source of record: `the November 2 reference manuscript`,
lines 1975-1979.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T15/2`** (weak product rule in the measure `s^{-3/2} ds`). -/
theorem weakProductRuleH2 : UnforcedLeray.Short.IIb.WeakProductRuleH2 :=
  weakProductRuleH2_of expChartIntegral logUMemLp logTestOfOrig logWeakTransfer logProductRule

end UnforcedLeray.Short.IIb
