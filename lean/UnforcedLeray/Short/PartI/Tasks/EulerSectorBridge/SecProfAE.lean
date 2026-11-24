import UnforcedLeray.Short.PartI.Sub.S11
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.Dense

/-!
# Part I, task `PartI:S11/1`: `secProfAE`

Source of record: `the November 2 reference manuscript`, lines 841-889.
Target: `SecProfAE` (`Short/PartI/Sub/S11.lean`).

Proof: `secProfAE_of` (`Short/PartI/Sub/PartI_S11_1.lean`) applied to the two leaves
`secAEOnSmoothSums` (task `PartI:S11/1/1`, `SecProfAE/OnSmoothSums.lean`) and
`smoothSectorSumsDense` (task `PartI:S11/1/2`, `SecProfAE/Dense.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:S11/1`.** The sector-`n` profile of `A_E f = (Kf)·∇E₀` is
`-couplingSec hM n` applied to the sector-`n` profile of `f`, for every `f ∈ H^0_M`. -/
theorem secProfAE : SecProfAE :=
  secProfAE_of secAEOnSmoothSums smoothSectorSumsDense

end UnforcedLeray.Short.PartI

end

#print axioms UnforcedLeray.Short.PartI.secProfAE
