import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L5_WardGradXPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L8_RepairSepBridge

/-!
# `PartIII-b:C/rep/2`: `PhaseGradient`

Source `the November 2 reference manuscript` lines 5203-5223 (`repair:phase-gradient`).
One-line application of `phaseGradient_of` (`Sub/PhaseGradient/Assembly.lean`) to
`repairSepBridge` (L8), `wardGradXPhase` (L5), and `wardGradYPhase` (L7).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phaseGradient (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.PhaseGradient :=
  phaseGradient_of repairSepBridge wardGradXPhase wardGradYPhase D hst

end UnforcedLeray.Short.PartIIIb.Concrete
