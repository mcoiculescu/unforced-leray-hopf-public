import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.AgeHolderHalf.BandDiffQuotient

/-!


Source of record: `the November 2 reference manuscript`,
lines 1758–1764, 1785–1788 (`near:local-smoothing`, flat stress age regularity).

Proves `flatStressAgeHolderHalf : FlatStressAgeHolderHalf` unconditionally by combining
`flatStressAgeHolderHalf_of` (`Sub/PartII-a_N05_4_2.lean`) with the unconditional positive-age
band Steklov bound `flatBandAgeDiffQuotient` (`AgeHolderHalf/BandDiffQuotient.lean` and
`AgeHolderHalf/MollifiedSteklov.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- Conditional proof of `FlatStressAgeHolderHalf` (`PartII-a:N05/4/2`) from the band age
difference-quotient leaf `FlatBandAgeDiffQuotient` (`PartII-a:N05/4/2/1`). -/
theorem flatStressAgeHolderHalf_of_leaves (hBand : FlatBandAgeDiffQuotient) :
    FlatStressAgeHolderHalf :=
  flatStressAgeHolderHalf_of hBand

/-- Unconditional proof of `FlatStressAgeHolderHalf` (`PartII-a:N05/4/2`). -/
theorem flatStressAgeHolderHalf : UnforcedLeray.Short.PartIIa.FlatStressAgeHolderHalf :=
  flatStressAgeHolderHalf_of flatBandAgeDiffQuotient

end UnforcedLeray.Short.PartIIa
