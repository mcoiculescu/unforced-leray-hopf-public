import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyFirstOrderLocal
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal

/-!


Target: `theorem bodyFlatLocalH1 : BodyFlatLocalH1`
(`the November 2 reference manuscript`,
lines 1794–1799).

Decomposed in `UnforcedLeray.Short.«PartII-a».Sub.«PartII-a_N05_2»` via `bodyFlatLocalH1_of`
into two leaf obligations:
- `FlatBodyFirstOrderLocal` (`PartII-a:N05/2/1`)
- `FlatBodyAgeDerivLocal` (`PartII-a:N05/2/2`)
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- Conditional assembly of `BodyFlatLocalH1` from the two leaf obligations in
`Sub/PartII-a_N05_2.lean`. -/
theorem bodyFlatLocalH1_of_leaves (hFirst : FlatBodyFirstOrderLocal)
    (hAge : FlatBodyAgeDerivLocal) : BodyFlatLocalH1 :=
  bodyFlatLocalH1_of hFirst hAge

/-- Target `PartII-a:N05/2`: local `H¹(s, q, η)` regularity of `χ T_0 b`. -/
theorem bodyFlatLocalH1 : UnforcedLeray.Short.PartIIa.BodyFlatLocalH1 :=
  bodyFlatLocalH1_of flatBodyFirstOrderLocal flatBodyAgeDerivLocal

end UnforcedLeray.Short.PartIIa
