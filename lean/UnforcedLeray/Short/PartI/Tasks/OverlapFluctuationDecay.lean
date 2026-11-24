import UnforcedLeray.Short.PartI.Sub.PartI_T13
import UnforcedLeray.Short.PartI.Sub.PartI_T13.SmoothL2
import UnforcedLeray.Short.PartI.Sub.PartI_T13.EnergyBalance

/-!
# `PartI:T13` (`Tasks/OverlapFluctuationDecay.lean`): exponential decay of the overlap fluctuation

Source of record: `the November 2 reference manuscript`, lines 304-313, 389-396
(old 354-362).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Exponential decay of the overlap horizontal fluctuation (`PartI:T13`)**
(source lines 304-313, 389-396). -/
theorem overlap_fluctuation_decay (hHN : OverlapHighNormUniform) : OverlapFluctuationDecay :=
  overlap_fluctuation_decay_of overlapFluctuationSmoothL2_proof
    (overlapFluctuationEnergyBalance_proof overlapFluctuationSmoothL2_proof) hHN

end UnforcedLeray.Short.PartI
