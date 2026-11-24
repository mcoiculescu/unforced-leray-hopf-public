import UnforcedLeray.Short.PartIIa.Sub.N02_4_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncMoment
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.TruncConverge

/-!
# Part II-a, task `PartII-a:N02/4/2` glue: `NzTruncApprox` from the three truncation lemmas

Pure assembly. The three lemmas `nzTruncTest` (N02/4/9), `nzTruncMoment` (N02/4/10) and
`nzTruncConverge` (N02/4/11) are fed into `nzTruncApprox_of` (proved in `Sub/N02_4_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`NzTruncApprox` (task N02/4/2), assembled from the three truncation lemmas.** -/
theorem nzTruncApprox : UnforcedLeray.Short.PartIIa.NzTruncApprox :=
  nzTruncApprox_of nzTruncTest nzTruncMoment nzTruncConverge

end UnforcedLeray.Short.PartIIa
