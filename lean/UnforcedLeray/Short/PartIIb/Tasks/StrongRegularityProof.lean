import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity

/-!
# `PartIII-b:C/rep/9/1/sr`: `StrongRegularity`

Source of record: `the November 2 reference manuscript`, lines 2525-2562.

Assembles `strongRegularity_proof` from `affineInletFacts_proof`, `quadBound_of`,
`strongFirstDerivative_of`, `strongAllOrders_of`, and `strongRegularity_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem strongRegularity_proof : UnforcedLeray.Short.IIb.StrongRegularity :=
  let h4 := affineInletFacts_proof
  let hQ1 := quadBound_of h4
  let hS1 := _root_.strongFirstDerivative_of h4 hQ1
  let hS2 := strongAllOrders_of h4 hQ1 hS1
  strongRegularity_of hS1 hS2

end UnforcedLeray.Short.IIb
