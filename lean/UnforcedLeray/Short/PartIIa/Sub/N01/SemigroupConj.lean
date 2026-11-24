import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_2
import UnforcedLeray.Short.PartIIa.Sub.N01.PhaseSliceFormula

/-!
# `PartII-a:N01/2`: `PhaseSemigroupConj` from the slice formula

Source of record `the November 2 reference manuscript`
lines 1363-1372. The slice formula `phaseSliceFormula` (leaf `N01/2/1`) gives the hypothesis of
`phaseSemigroupConj_of`, which is the conclusion `PhaseSemigroupConj`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem phaseSemigroupConj : UnforcedLeray.Short.PartIIa.N01.PhaseSemigroupConj :=
  phaseSemigroupConj_of phaseSliceFormula

end UnforcedLeray.Short.PartIIa.N01
