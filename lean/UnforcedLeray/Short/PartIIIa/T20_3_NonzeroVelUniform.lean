import UnforcedLeray.Short.PartIIIa.Sub.T20_3
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.FirstMoment
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.L1Integrable
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.ZeroMassModeBound
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.FourierL2Formulas
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.WeightedIntegralBound

/-!
# Part III-a, task `PartIII-a:T20/3`: the uniform nonzero-mode velocity bound

Assembly only. The conditional theorem `T20_3.nonzeroVelUniform_of` (in `Sub/T20_3.lean`) is
combined with the five accepted leaves `T20_3.firstMomentBound`, `T20_3.l1Integrable`,
`T20_3.zeroMassModeBound`, `T20_3.fourierL2Formulas` and `T20_3.weightedIntegralBound`.
Source of record: `the November 2 reference manuscript`, lines 3236-3240.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.CTE

theorem nonzeroVelUniform : NonzeroVelUniform :=
  T20_3.nonzeroVelUniform_of T20_3.firstMomentBound T20_3.l1Integrable
    T20_3.zeroMassModeBound T20_3.fourierL2Formulas T20_3.weightedIntegralBound

end UnforcedLeray.Short.IIIa.CTE

end
