import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04
import UnforcedLeray.Short.PartIIa.Tasks.F03LocalWindow
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY

/-!
# Part II-a, task `PartII-a:F04`: the maximal distributional domain

Source of record: `the November 2 reference manuscript`, lines 1409-1412 and
1470-1480.  Assembles the local window estimate `PartII-a:F03`
(`Tasks/F03LocalWindow.lean`), the global window Laplacian field `PartII-a:F04/1`
(`Tasks/F04aGlobalField.lean`) and the field-to-`Y_r` step `PartII-a:F04/2`
(`Tasks/F04bFieldToY.lean`) through `commonBodyMaximalDomain_of` (`Sub/PartIIa_F04.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F04`**: the maximal distributional domain `CommonBodyMaximalDomain`. -/
theorem commonBodyMaximalDomain : CommonBodyMaximalDomain :=
  commonBodyMaximalDomain_of localWindowEstimate globalLaplacianField laplacianFieldToY

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.commonBodyMaximalDomain
