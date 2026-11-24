import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.AxisNull
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L3_SepX0PhaseBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L4_OutPrimPhaseBound

/-!
# `PartIII-b:C/rep/2/5`: `WardGradXPhase` from its three leaves and S2, S3a

Source `the November 2 reference manuscript` 4161-4192, 5212-5217.
The leaves `wgxPointwise`, `wgxMeas`, `wgxAxisNull` and the phase bounds `sepX0PhaseBound`
(L3) and `outPrimPhaseBound` (L4) are composed through `wardGradXPhase_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`WardGradXPhase` (source 4181-4192, 5212-5217).** -/
theorem wardGradXPhase : WardGradXPhase :=
  wardGradXPhase_of wgxPointwise wgxMeas wgxAxisNull sepX0PhaseBound outPrimPhaseBound

end UnforcedLeray.Short.PartIIIb.Concrete

end
