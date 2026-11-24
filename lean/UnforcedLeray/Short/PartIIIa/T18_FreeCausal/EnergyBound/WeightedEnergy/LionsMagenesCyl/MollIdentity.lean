import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Deriv

/-!
# `PartIII-a:T18/3/1/3/2` (`MollIdentity`): the mollified energy identity

Assembles `MollifiedEnergyIdentity` from `lmEnergyBridge` (`LMEnergyBridge`) and
`mollDerivData` (`MollDerivData`) via `mollifiedEnergyIdentity_of`.
Source: `the November 2 reference manuscript` 3541-3552, 3427-3440.
-/

set_option autoImplicit false

theorem mollifiedEnergyIdentity : UnforcedLeray.Short.IIIa.MollifiedEnergyIdentity :=
  UnforcedLeray.Short.IIIa.mollifiedEnergyIdentity_of
    UnforcedLeray.Short.IIIa.lmEnergyBridge UnforcedLeray.Short.IIIa.mollDerivData
