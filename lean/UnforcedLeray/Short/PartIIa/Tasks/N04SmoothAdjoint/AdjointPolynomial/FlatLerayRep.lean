import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_1
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatLerayRep.IterDecay
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatLerayRep.MomentNorm

/-!


Closes `theorem flatLeraySmoothRep : FlatLeraySmoothRep` via
`flatLeraySmoothRep_of flatLerayIterDecay flatLerayMomentNormBound`
(leaves `PartII-a:N04/2/1/1` and `PartII-a:N04/2/1/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem flatLeraySmoothRep : FlatLeraySmoothRep :=
  flatLeraySmoothRep_of flatLerayIterDecay flatLerayMomentNormBound

end UnforcedLeray.Short.PartIIa
