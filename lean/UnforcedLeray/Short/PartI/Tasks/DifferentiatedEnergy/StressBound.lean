import UnforcedLeray.Short.PartI.Sub.PartI_T08_10
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcPeriodic

/-!
# Part I, task `PartI:T08/10` (`vcStressJetBound_proof`): assembly

Source: `the November 2 reference manuscript` lines 331-335.
Assembles `vcStressJetBound_of` (in `Sub/PartI_T08_10.lean`) with the leaves
`qcSmooth_proof` (`PartI:T08/1/2`) and `qcPeriodic_proof` (`PartI:T08/1/3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem vcStressJetBound_proof : UnforcedLeray.Short.PartI.VcStressJetBound :=
  vcStressJetBound_of qcSmooth_proof qcPeriodic_proof

end UnforcedLeray.Short.PartI
