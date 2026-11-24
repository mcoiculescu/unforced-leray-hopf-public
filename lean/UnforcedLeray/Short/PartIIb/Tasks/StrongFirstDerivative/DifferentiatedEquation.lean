import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.LinBound
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation.QuadBound

/-!
# `PartII-b:S1/1`: Differentiated equation graph bound (`DifferentiatedEquationGraphBound`, SP 2525-2537)

Assembly from the two leaves `diffEqLinBound_proof` (`PartII-b:S1/1/1`) and
`diffEqQuadBound_proof` (`PartII-b:S1/1/2`) via `differentiatedEquationGraphBound_of_leaves`.
-/

namespace UnforcedLeray.Short.IIb

theorem differentiatedEquationGraphBound_of
    (h4 : UnforcedLeray.Short.IIb.AffineInletFacts)
    (hQ1 : UnforcedLeray.Short.IIb.QuadBound) :
    UnforcedLeray.Short.IIb.DifferentiatedEquationGraphBound :=
  differentiatedEquationGraphBound_of_leaves diffEqLinBound_proof diffEqQuadBound_proof h4 hQ1

end UnforcedLeray.Short.IIb
