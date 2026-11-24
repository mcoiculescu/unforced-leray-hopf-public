import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyEpsLocalH1
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14

/-!


Source of record: `the November 2 reference manuscript`, lines 1751-1799
(`near:local-smoothing`).

Assembles `nearLocalRegularity` from `nearLocalRegularity_of`, `bodyEpsLocalH1`,
`bodyFlatLocalH1`, `stressEpsLocalH14`, and `stressFlatLocalH14`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem nearLocalRegularity : UnforcedLeray.Short.PartIIa.NearLocalRegularity :=
  nearLocalRegularity_of bodyEpsLocalH1 bodyFlatLocalH1 stressEpsLocalH14 stressFlatLocalH14

end UnforcedLeray.Short.PartIIa
