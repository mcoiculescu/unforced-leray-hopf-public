import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.AgeHolderHalf

/-!


Source of record: `the November 2 reference manuscript`, lines 1757-1764,
1785-1788 (`near:local-smoothing`, flat stress case).

Assembles `stressFlatLocalH14` from `stressFlatLocalH14_of`, `flatStressSpatialHolderHalf`,
and `flatStressAgeHolderHalf`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem stressFlatLocalH14 : UnforcedLeray.Short.PartIIa.StressFlatLocalH14 :=
  stressFlatLocalH14_of flatStressSpatialHolderHalf flatStressAgeHolderHalf

end UnforcedLeray.Short.PartIIa
