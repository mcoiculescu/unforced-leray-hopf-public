import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_2_2
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.HelmholtzApprox
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode.WeakModeIntegrable

/-!
# `PartIII-b:IIIb-D5/2/2`: `WeakDmuToPeriodicModeEq`
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux

theorem weakDmuToPeriodicModeEq_proved : WeakDmuToPeriodicModeEq :=
  weakDmuToPeriodicModeEq_of _root_.helmholtzApprox_proved _root_.weakModeIntegrable_proved

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux
