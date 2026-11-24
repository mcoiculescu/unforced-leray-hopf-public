import UnforcedLeray.Short.PartIIIa.Sub.T18_2_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.TCalNormTriangle
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.CompleteH
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.CompleteT
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceAE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.EnergyPerturb
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.SliceClauses
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE.FlatIntegrandBound

/-!
# Part III-a, task `PartIII-a:T18/2/1`: the unconditional `L²` limit of causal solutions

Proves `UnforcedLeray.Short.IIIa.CausalLimitAE` (statement in `Sub/T18_2.lean`, source of record
`the November 2 reference manuscript`, lines 3427-3440, "let `δ → 0`").

The assembly is `causalLimitAE_of` (`Sub/T18_2_1.lean`), applied to the seven leaf theorems:
`tCalNormTriangle`, `causalCompleteH`, `causalCompleteT`, `causalSliceAE`, `causalEnergyPerturb`,
`causalSliceClauses`, `flatIntegrandBound`. Each leaf is proved in its own module under
`T18_FreeCausal/Existence/` (and `CausalLimitAE/`).
-/

namespace UnforcedLeray.Short.IIIa

theorem causalLimitAE : UnforcedLeray.Short.IIIa.CausalLimitAE :=
  causalLimitAE_of tCalNormTriangle causalCompleteH causalCompleteT causalSliceAE
    causalEnergyPerturb causalSliceClauses flatIntegrandBound

end UnforcedLeray.Short.IIIa
