import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_3
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HardyGradKernel.HardyBetaFinite
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HardyGradKernel.HardySubst
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HardyGradKernel.HardyMinkowski

/-!
# `PartII-a:N01/9/1/3/3/2/1/3`: `HardyGradKernel`

Source `the November 2 reference manuscript`
lines 1684-1689, 3541-3552.  Assembly of the three lemmas `HardyBetaFinite` (H1), `HardySubst` (H2)
and `HardyMinkowski` (H3) through `hardyGradKernel_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

theorem hardyGradKernel : UnforcedLeray.Short.PartIIa.N01.HardyGradKernel :=
  hardyGradKernel_of hardyBetaFinite hardySubst hardyMinkowski

end UnforcedLeray.Short.PartIIa.N01
