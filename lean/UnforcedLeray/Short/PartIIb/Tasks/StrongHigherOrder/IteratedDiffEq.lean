import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawAllDerivsBdd
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.RawResidualIteratedEnvelope
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedInletDerivY
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedQuadDerivY

/-!
# `PartII-b:S2/1`: Higher-order differentiated equation in `Y_p` (`IteratedDiffEqInYq`, SP 2541-2559)

Assembles `iteratedDiffEqInYq_proof` from `iteratedDiffEqInYq_of_sub`, `rawAllDerivsBdd_proof`,
`rawResidualIteratedEnvelope_proof`, `iteratedInletDerivY_proof`, `iteratedQuadDerivY_proof`,
and `hS1 : StrongFirstDerivative`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem iteratedDiffEqInYq_proof (hS1 : UnforcedLeray.Short.IIb.StrongFirstDerivative) :
    UnforcedLeray.Short.IIb.IteratedDiffEqInYq :=
  iteratedDiffEqInYq_of_sub rawAllDerivsBdd_proof rawResidualIteratedEnvelope_proof
    iteratedInletDerivY_proof iteratedQuadDerivY_proof hS1

end UnforcedLeray.Short.IIb
