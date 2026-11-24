import UnforcedLeray.Short.PartI.Sub.PartI_T04_8
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticA
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticB
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticD

/-!


Source: `the November 2 reference manuscript` lines 285-287. The four
ingredients `apEllipticA`, `apEllipticB`, `apEllipticC`, `apEllipticD` (tasks `PartI:T04/8/1..4`)
assemble into `APElliptic` by `apElliptic_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

theorem apElliptic : APElliptic :=
  apElliptic_of apEllipticA apEllipticB apEllipticC apEllipticD

end UnforcedLeray.Short.PartI
