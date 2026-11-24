import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S1
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.DifferentiatedEquation
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative.ContRepFDeriv

/-!
# `PartII-b:S1`: First spatial derivative in the maximal graph and `W^{1,∞}` / `L^p` bounds (SP 2525-2541)

Decomposed via `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S1»`: once `PartII-b:S1/1`
(`differentiatedEquationGraphBound_of : AffineInletFacts → QuadBound → DifferentiatedEquationGraphBound`
in `UnforcedLeray.Short.«PartII-b».Tasks.StrongFirstDerivative.DifferentiatedEquation`) and
`PartII-b:S1/2` (`contRepFDerivLeSumGrad_proof : ContRepFDerivLeSumGrad` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongFirstDerivative.ContRepFDeriv`) are proved, assemble:

```lean
theorem strongFirstDerivative_of (h4 : UnforcedLeray.Short.IIb.AffineInletFacts)
    (hQ1 : UnforcedLeray.Short.IIb.QuadBound) : UnforcedLeray.Short.IIb.StrongFirstDerivative :=
  strongFirstDerivative_of_parts (differentiatedEquationGraphBound_of h4 hQ1)
    contRepFDerivLeSumGrad_proof h4 hQ1
```
-/

set_option autoImplicit false

open UnforcedLeray.Short.IIb in
theorem strongFirstDerivative_of (h4 : UnforcedLeray.Short.IIb.AffineInletFacts)
    (hQ1 : UnforcedLeray.Short.IIb.QuadBound) : UnforcedLeray.Short.IIb.StrongFirstDerivative :=
  strongFirstDerivative_of_parts (differentiatedEquationGraphBound_of h4 hQ1)
    contRepFDerivLeSumGrad_proof h4 hQ1
