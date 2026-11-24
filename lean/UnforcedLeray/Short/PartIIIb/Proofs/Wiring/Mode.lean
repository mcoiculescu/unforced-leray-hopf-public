import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_2
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.StressInvH1Grad
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.WeakDmuToPeriodicModeEq

/-!
# `PartIII-b:IIIb-D5/2`: `Wiring.ModeOfReturn`

Source of record: `the November 2 reference manuscript`, lines 5969–5985.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem modeOfReturn : Wiring.ModeOfReturn :=
  modeOfReturn_of stressInvH1Grad_proved Wiring.ModeAux.weakDmuToPeriodicModeEq_proved

end UnforcedLeray.Short.PartIIIb.Concrete
