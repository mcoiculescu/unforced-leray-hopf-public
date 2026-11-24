import UnforcedLeray.Short.PartIIa.Sub.N01.Reduction
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatReduction

/-!
# `PartII-a:N01` (design): `NearStressMapExists` from the eleven leaves

Source of record: `the November 2 reference manuscript`,
lines 1675-1689 (`near:free-energy` and the flat age-energy estimate), with 1339-1372, 1546-1567,
1625-1632 (the Cartesian foundation and the transported stress map).

Leaves (tasks): `PhaseLiftExists` (`N01/1`), `PhaseSemigroupConj` (`/2`), `PhaseLerayConj` (`/3`),
`PhaseDivScale` (`/4`), `CartLiftRows` (`/5`), `CartLiftNorm` (`/6`), `TensorTestReIm` (`/7`),
`StressCompletion` (`/8`) in `Sub/N01/Defs.lean`; `FlatColumnC` (`/9`), `FlatVelTransport` (`/10`),
`FlatBlkTransport` (`/11`) in `Sub/N01/FlatReduction.lean`.  The unconditional target is task
`PartII-a:N01` (`Tasks/N01StressMaps.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

/-- **`NearStressMapExists` from the eleven leaf Props.** -/
theorem nearStressMapExists_of_leaves (h1 : PhaseLiftExists) (h2 : PhaseSemigroupConj)
    (h3 : PhaseLerayConj) (h4 : PhaseDivScale) (h5 : CartLiftRows) (h6 : CartLiftNorm)
    (h7 : TensorTestReIm) (h8 : StressCompletion) (h9 : FlatColumnC) (h10 : FlatVelTransport)
    (h11 : FlatBlkTransport) : NearStressMapExists :=
  nearStressMapExists_of_parts h1 h2 h3 h4 h5 h6 h7 h8 (flatSmoothBound_of h9 h10 h11)

end UnforcedLeray.Short.PartIIa.N01
