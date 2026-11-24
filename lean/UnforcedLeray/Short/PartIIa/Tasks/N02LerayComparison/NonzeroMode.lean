import UnforcedLeray.Short.PartIIa.Sub.N02_4
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.CutoffApprox
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncApprox
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FlatMembership
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials

/-!
# Part II-a, task `PartII-a:N02/4` glue: `NearLerayNonzeroMode` from the four lemma files

Pure assembly. `nearLerayNonzeroMode_of` (proved in `Sub/N02_4.lean`) is fed with
`nzTruncApprox` (N02/4/2), `nzFinPotentials` (N02/4/3), `nzFlatMembership` (N02/4/4)
and `nzCutoffApprox` (N02/4/1).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`NearLerayNonzeroMode` (task N02/4), assembled from the four lemma Props.** -/
theorem nearLerayNonzeroMode_proof : UnforcedLeray.Short.PartIIa.NearLerayNonzeroMode :=
  nearLerayNonzeroMode_of nzTruncApprox nzFinPotentials nzFlatMembership nzCutoffApprox

end UnforcedLeray.Short.PartIIa
