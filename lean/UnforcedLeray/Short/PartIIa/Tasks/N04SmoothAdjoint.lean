import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.ObsBoxS1
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.GradDiffIBP

/-!
# N04: Smooth Adjoint Comparison on Boxed Observables

Target: `theorem nearSmoothAdjointComparison : NearSmoothAdjointComparison`
(Lemma `near:smooth-adjoint-comparison` and Lemma `near:adjoint-polynomial`,
`shorter-proof-2026-11-02.tex` lines 1757–1869).

Decomposed in `UnforcedLeray.Short.«PartII-a».Sub.«PartII-a_N04»` into four leaf
obligations:
- `ObsBoxS1Bound` (`PartII-a:N04/1`)
- `AdjointPolynomialBound` (`PartII-a:N04/2`)
- `AdjointResidualEq` (`PartII-a:N04/3`)
- `GradDiffIBP` (`PartII-a:N04/4`)

Once the four leaf tasks are proved, `nearSmoothAdjointComparison` follows immediately from
`nearSmoothAdjointComparison_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem nearSmoothAdjointComparison : NearSmoothAdjointComparison :=
  nearSmoothAdjointComparison_of obsBoxS1Bound adjointPolynomialBound adjointResidualEq gradDiffIBP

end UnforcedLeray.Short.PartIIa
