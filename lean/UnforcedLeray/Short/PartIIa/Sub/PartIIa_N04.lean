import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.Defs
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.SymGrad

/-!
# Sub/PartII-a_N04: Smooth Adjoint Comparison Reduction

Assembles the reduction of `NearSmoothAdjointComparison` (`PartII-a:N04`) to four leaf
obligations:
- `ObsBoxS1Bound` (`PartII-a:N04/1`)
- `AdjointPolynomialBound` (`PartII-a:N04/2`)
- `AdjointResidualEq` (`PartII-a:N04/3`)
- `GradDiffIBP` (`PartII-a:N04/4`)

with `SymGradAdjointBound` already discharged unconditionally in `SymGrad.lean`.
-/

namespace UnforcedLeray.Short.PartIIa

/-- Reduction of `NearSmoothAdjointComparison` to the 4 remaining leaf obligations
(with `symGradAdjointBound` already proved in `Sub/PartII-a_N04/SymGrad.lean`). -/
theorem nearSmoothAdjointComparison_of (hObs : ObsBoxS1Bound)
    (hPoly : AdjointPolynomialBound) (hRes : AdjointResidualEq) (hIBP : GradDiffIBP) :
    NearSmoothAdjointComparison :=
  nearSmoothAdjointComparison_of_five hObs hPoly hRes symGradAdjointBound hIBP

end UnforcedLeray.Short.PartIIa
