import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.IntegratedH1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutE1Deriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutRateBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutE1TimeCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutSliceProps
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutEnergySqueeze
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.L2StrongOfEnergy
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.GradEIntegrable

/-!
# `PartIII-a:T21/2/7/2/3`: weighted `H¹` continuity of the adjoint

Assembly of `adjointWeakH1Cont_of` (`Sub/PartIIIa_T21_2_7_2.lean` / `Sub/PartIII-a_T21_2_7_2_3.lean`)
from `adjointIntegratedH1`, `adjWeakChiBound`, and the leaves `cutE1Deriv`, `cutRateBound`,
`cutE1TimeCont`, `cutSliceProps`, `cutEnergySqueeze`, `l2StrongOfEnergy`, `gradEIntegrable`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjointWeakH1Cont (m : ℝ) (hm : 8 < m) : AdjointWeakH1Cont m :=
  adjointWeakH1Cont_of m (adjointIntegratedH1 m hm) (adjWeakChiBound m hm) cutE1Deriv
    cutRateBound cutE1TimeCont cutSliceProps cutEnergySqueeze l2StrongOfEnergy gradEIntegrable

end UnforcedLeray.Short.IIIa
