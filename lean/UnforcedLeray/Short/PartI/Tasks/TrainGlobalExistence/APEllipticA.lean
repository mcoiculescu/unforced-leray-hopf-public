import UnforcedLeray.Short.PartI.Sub.PartI_T04_8_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticAInt
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticAEq

/-!


Source: `the November 2 reference manuscript` lines 285-287. The integrability
statement `apEllipticAInt` (task `PartI:T04/8/1/1`) and the cell identity `apEllipticAEq`
(task `PartI:T04/8/1/2`) assemble into `APEllipticA` by `apEllipticA_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

theorem apEllipticA : APEllipticA :=
  apEllipticA_of apEllipticAInt apEllipticAEq

end UnforcedLeray.Short.PartI
